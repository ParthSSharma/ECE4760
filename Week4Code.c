/*
Authors: Shreyas Patil, Parth Sarthi Sharma
Affiliation: Cornell University
Course: ECE 4760
Purpose: Week 4 of Final Project
*/

#include "config_1_3_2.h" //Contains the main configurations like clock freq etc.
#include "pt_cornell_1_3_2_python.h" //Threading library
#include "tft_master.h" //Library used to use the TFT screen
#include "tft_gfx.h" //Library used to draw on the TFT screen
#include <stdlib.h> //Standard C library
#include <stdfix.h> //Library for importing the fixed-point datatype
#include <math.h> //Library with all math functions
#include "BitMap.h" //Include the bitmap library
#include "Audio.h" //Include the audio library

#define HEIGHT 240 //Height of the TFT screen
#define WIDTH 320 //Width of the TFT screen

#define SCORE_X_OFFSET1 5 //x offset for text
#define SCORE_X_OFFSET2 150 //x offset for variables
#define SCORE_Y_OFFSET1 5 //y offset for score
#define SCORE_Y_OFFSET2 30 //y offset for high score

#define GROUND_SIZE 10 //Number of elements in the ground array
#define GROUND_HEIGHT 60 //Height of the ground above the base

#define OBS_W_0 10 //Width of obstacle type 0
#define OBS_H_0 20 //Height of obstacle type 0
#define OBS_W_1 15 //Width of obstacle type 1
#define OBS_H_1 30 //Height of obstacle type 1
#define OBS_W_2 30 //Width of obstacle type 2
#define OBS_H_2 20 //Height of obstacle type 2

#define SPEED 5 //Speed with which the ground moves
#define GRAVITY 1.2 //The gravity value
#define JUM_VEL 15 //Velocity with which the dino jumps
#define RUNNER_FRAMES 10 //Used for alternating between 2 dino running bitmaps

#define HARD_COLOR 0x632C //Display white
#define SOFT_COLOR 0x2945 //Display grayish color
#define BG_COLOR 0x0841 //The background color

#define F 40000000 //Clock frequency
#define Fs 4000 //Sampling frequency

//Paramters to be used to work with ADC
#define PARAM1 ADC_FORMAT_INTG16 | ADC_CLK_AUTO | ADC_AUTO_SAMPLING_OFF
#define PARAM2 ADC_VREF_AVDD_AVSS | ADC_OFFSET_CAL_DISABLE | ADC_SCAN_OFF | ADC_SAMPLES_PER_INT_1 | ADC_ALT_BUF_OFF | ADC_ALT_INPUT_OFF
#define PARAM3 ADC_CONV_CLK_PB | ADC_SAMPLE_TIME_5 | ADC_CONV_CLK_Tcy2
#define PARAM4 ENABLE_AN11_ANA
#define PARAM5 SKIP_SCAN_ALL

#define nSamp 512 //Number of samples in each iteration of FFT
#define nPixels 256 //Number of pixels to be represented. It is 256 as the bottom 256 are symmetrical to the top 256
#define N_WAVE 512 //Number of entries for the sinewave and window function
#define LOG2_N_WAVE 9 //log2(512)

#define FREQ_UPPER 1800 //Upper frequency for voice detection
#define FREQ_LOWER 1500 //Lower frequency for voice detection

#define float2Accum(a) ((_Accum)(a)) //Convert a floating point number to an Accum
#define Accum2float(a) ((float)(a)) //Convert an Accum to a floating point number
#define int2Accum(a) ((_Accum)(a)) //Convert an int to an Accum
#define Accum2int(a) ((int)(a)) //Convert an Accum to an int

#define log_min 0x10 //Used to compute the log

#define JUMP_AUDIO_SIZE 23156 //Number of bytes in the jump audio
#define DEAD_AUDIO_SIZE 35670 //Number of bytes in the dead audio
#define DMA_CHANNEL2 2 //DMA channel 2
#define DMA_CHANNEL3 3 //DMA channel 3
#define SPI_CLK_DIV 2 //SPI clock divider

int exTime; //Time to yield the animation protothread
int obsType; //Variable to keep track of the obstacle type

char startGame = 0; //The flag to check if the game has started
char runner = 0; //The variable to store which how many frames have elapsed since the running bitmap was changed
int score = 0, highScore = 0; //Score and high score

char buffer[60]; //Buffer to display the strings on the TFT
char newButton = 0; //New button flag to check if a GUI button has been pressed
char buttonID, buttonValue; //Button ID and value to see what button event has occurred and if the button was pressed or released

_Accum v_in[nSamp]; //Fixed point input array
_Accum Sinewave[N_WAVE]; //The sine wave array of 512 elements
_Accum window[N_WAVE]; //The Hann window array
_Accum fr[N_WAVE], fi[N_WAVE]; //The input real and imaginary arrays
_Accum maxFreq; //The maximum frequency

volatile int adc_9 = 0; //Input from ADC
int counter = 0; //Counter variable

struct Ground{ //Ground structure to store each small ground element with x-coordinate, y-coordinate and width
    int x, y, w;
};

struct Obstacle{ //Obstacle structure to store the x-coordinate, y-coordinate and width of the obstacle
    int x, w, h;
};

struct Player{ //Player structure to store the x-coordinate, y-coordinate, width, height, velocity and alive status of the dino
    int x, y, w, h, vy;
    int alive;
};

#define pgm_read_byte(addr) (*(const unsigned char *)(addr)) //Function to check if an individual bit is set
void drawBitmap(short x, short y, const unsigned char *bitmap, short w, short h, unsigned short color){ //Optimized function for bitmap implementation
    if((x >= _width) || (y >= _height)) return; //If the image to be drawn is completely out of frame, return
    if((x + w - 1) >= _width)  w = _width  - x; //Optimize the width in case a part of it is outside the screen
    if((y + h - 1) >= _height) h = _height - y; //Optimize the height in case a part of it is outside the screen

    tft_setAddrWindow(x, y, x + w - 1, y + h - 1); //Set the address window of the image
    _dc_high();
    _cs_low();
  
    short i, j, byteWidth = (w + 7) / 8;
    for(j = 0; j < h; j++){ //Traverse through rows
        for(i = 0; i < w; i++){ //Traverse through columns
            if(pgm_read_byte(bitmap + j * byteWidth + i / 8) & (128 >> (i & 7))) { //If the given is set
                tft_spiwrite16(color); //Write the color to the TFT
            }
            else{ //Otherwise
                tft_spiwrite16(BG_COLOR); //Write the black color to the TFT. Change this if you want to use a different background color
            }
        }
    }
  _cs_high();
}

inline int randomRange(int min, int max){ //Function to generate a random number between min and max
    return (rand() % (max - min)) + min;
}

struct Ground ground[GROUND_SIZE]; //Ground array
struct Obstacle obstacle; //The obstacle object
struct Player myPlayer; //The player object

//The interrupt handler
void __ISR(_TIMER_2_VECTOR, ipl2) Timer2Handler(void){
    mT2ClearIntFlag(); //You MUST clear the ISR flag
    adc_9 = ReadADC10(0); //Read the ADC value and put it in adc_9
    AcquireADC10(); //Start the process of acquiring the value of ADC for the next cycle
    
    v_in[counter] = int2Accum(adc_9); //Fill the value in the appropriate index in v_in
    counter++; //Increment the counter
    if(counter == nSamp){ //If the counter reaches the limit
        counter = 0; //Reset the counter
    }
}

//The FFT function
void FFTfix(_Accum fr[], _Accum fi[], int m){ //The real array, the imaginary array and the LOG2_N_WAVE
    int mr, nn, i, j, L, k, istep, n; //The counter variables
    _Accum qr, qi, tr, ti, wr, wi; //The calculation variables

    mr = 0;
    n = 1 << m;
    nn = n - 1;
    for(m = 1; m <= nn; ++m){
        L = n;
        do{
            L >>= 1;
        }
        while(mr + L > nn);
        mr = (mr & (L - 1)) + L;
        if(mr <= m){
            continue;
        }
        tr = fr[m];
        fr[m] = fr[mr];
        fr[mr] = tr;
    }

    L = 1;
    k = LOG2_N_WAVE - 1;
    while(L < n){
        istep = L << 1;
        for(m = 0; m < L; ++m){
            j = m << k;
            wr =  Sinewave[j + N_WAVE / 4];
            wi = -Sinewave[j];
            for(i = m; i < n; i += istep){
                j = i + L;
                tr = (wr * fr[j]) - (wi * fi[j]);
                ti = (wr * fi[j]) + (wi * fr[j]);
                qr = fr[i] >> 1;
                qi = fi[i] >> 1;
                fr[j] = qr - tr;
                fi[j] = qi - ti;
                fr[i] = qr + tr;
                fi[i] = qi + ti;
            }
        }
        --k;
        L = istep;
    }
}

static PT_THREAD (protothread_serial(struct pt *pt)){ //Python serial thread
    PT_BEGIN(pt);
    static char junk;
    while(1){
        // There is no YIELD in this loop because there are
        // YIELDS in the spawned threads that determine the 
        // execution rate while WAITING for machine input
        // =============================================
        // NOTE!! -- to use serial spawned functions
        // you MUST edit config_1_3_2 to
        // (1) uncomment the line -- #define use_uart_serial
        // (2) SET the baud rate to match the PC terminal
        // =============================================
        
        // now wait for machine input from python
        // Terminate on the usual <enter key>
        PT_terminate_char = '\r'; 
        PT_terminate_count = 0; 
        PT_terminate_time = 0;
        // note that there will NO visual feedback using the following function
        PT_SPAWN(pt, &pt_input, PT_GetMachineBuffer(&pt_input));
        // Parse the string from Python
        if (PT_term_buffer[0] == 'b'){ //Pushbutton
            newButton = 1; //Signal the button thread
            //Subtracting '0' converts ascii to binary for 1 character
            buttonID = (PT_term_buffer[1] - '0') * 10 + (PT_term_buffer[2] - '0');
            buttonValue = PT_term_buffer[3] - '0';
        }
    }
    PT_END(pt);
}

static PT_THREAD (protothread_buttons(struct pt *pt)){ //Buttons thread
    PT_BEGIN(pt);
    while(1){
        PT_YIELD_UNTIL(pt, newButton == 1);
        newButton = 0; //Clear flag
        if(buttonID == 2 && buttonValue == 1 && myPlayer.y == 0 && startGame){ //If the button 2 was pressed and the game has started
            myPlayer.vy = JUM_VEL; //Set dino's velocity to be JUM_VEL
            myPlayer.y += 1; //Make dino jump a little
            DmaChnEnable(DMA_CHANNEL2); //Play the jump audio
        }
        else if(buttonID == 1 && buttonValue == 1 && startGame == 0){ //If the button 1 was pressed and the game has not started
            startGame = 1; //Start the game
            tft_fillRect(0, 0, WIDTH, HEIGHT, BG_COLOR); //Clear the screen
            tft_setTextSize(2); //Set text size
            tft_setTextColor(SOFT_COLOR); //Set text color
            tft_setCursor(SCORE_X_OFFSET1, SCORE_Y_OFFSET1); //Set text coordinates
            tft_writeString("Your Score:"); //Print the text
            tft_setCursor(SCORE_X_OFFSET1, SCORE_Y_OFFSET2); //Set text coordinates
            tft_writeString("High Score:"); //Print the text
            tft_setCursor(SCORE_X_OFFSET2, SCORE_Y_OFFSET1); //Set text coordinates
            sprintf(buffer, "%2d", score); //Send the score into the buffer array
            tft_writeString(buffer); //Print the text
            tft_setCursor(SCORE_X_OFFSET2, SCORE_Y_OFFSET2); //Set text coordinates
            sprintf(buffer, "%2d", highScore); //Send the high score into the buffer array
            tft_writeString(buffer); //Print the text
        }
        else if(buttonID == 3 && buttonValue == 1){ //If the button 3 was pressed
            startGame = 0; //Reset the start flag
            tft_fillRect(0, 0, WIDTH, HEIGHT, BG_COLOR); //Clear the screen
            tft_setTextSize(4); //Set text size to be 4
            tft_setTextColor(SOFT_COLOR); //Set the text color to be SOFT_COLOR
            tft_setCursor(25, 100); //Set the cursor at 25, 100
            tft_writeString("Press Start!"); //Write "Press Start!"

            obsType = randomRange(0, 3); //Get a random obstacle type
            obstacle.x = WIDTH; //Set its x-coordinate to the right most edge
            if(obsType == 0){ //If it is obstacle type 0
                obstacle.w = OBS_W_0; //Set obstacle width to predefined width
                obstacle.h = OBS_H_0; //Set obstacle height to predefined height
            }
            else if(obsType == 1){ //If it is obstacle type 1
                obstacle.w = OBS_W_1; //Set obstacle width to predefined width
                obstacle.h = OBS_H_1; //Set obstacle height to predefined height
            }
            else{ //If it is obstacle type 2
                obstacle.w = OBS_W_2; //Set obstacle width to predefined width
                obstacle.h = OBS_H_2; //Set obstacle height to predefined height
            }

            myPlayer.y = 0; //Reset the y-coordinate of the player
            myPlayer.vy = 0; //Reset the velocity of the player
            myPlayer.alive = 1; //Make the player alive
            score = 0; //Reset the score
        }
    }
    PT_END(pt);
}

static PT_THREAD (pt_anim(struct pt *pt)){ //Animation protothread
    PT_BEGIN(pt); //Begin the protothread
    static unsigned int begin_time, i; //Variable to keep track of start time and counter i
    static int sample_number; //The sample number index
    static _Accum zero_point_4 = float2Accum(0.4); //Floating point 0.4
    while(1){ //Infinite while loop
        begin_time = PT_GET_TIME(); //Get start time
        if(startGame & myPlayer.alive){ //If the game has been started and the player is alive
            for (sample_number = 0; sample_number < nSamp - 1; sample_number++){ //For each sample
                fr[sample_number] = v_in[sample_number] * window[sample_number]; //Window the input using Hann window
                fi[sample_number] = 0; //Set the imaginary part to 0
            }
            FFTfix(fr, fi, LOG2_N_WAVE); //Compute the fixed point FFT

            for (sample_number = 0; sample_number < nPixels; sample_number++){  //For the bottom 256 samples
                fr[sample_number] = abs(fr[sample_number]); //Get the magnitude of the real part
                fi[sample_number] = abs(fi[sample_number]); //Get the magnitude of the imaginary part
                fr[sample_number] = max(fr[sample_number], fi[sample_number]) + (min(fr[sample_number], fi[sample_number]) * zero_point_4); //Store the magnitude of the result in the real array
            }

            static maxPower = 3; //Let the max index start from 3 (We do not start from 0 because there is a DC offset for very low frequency)
            for(sample_number = 3; sample_number <= nPixels; sample_number++){ //For each sample starting from 3
                if(fr[sample_number] > fr[maxPower]){ //If the current index holds power greater than the maxPower index bin
                    maxPower = sample_number; //Update the maxPower index
                }
            }

            maxFreq = ((int2Accum(Fs) / int2Accum(512)) * int2Accum(maxPower)); //Compute the maxFreq using maxPower
            printf("Max Poweprintfr: %d\n", Accum2int(maxFreq)); //Print the maximum frequency
            if(maxFreq < int2Accum(FREQ_UPPER) && maxFreq > int2Accum(FREQ_LOWER) && myPlayer.y == 0){ //If the maximum frequency is within the range
                myPlayer.vy = JUM_VEL; //Set dino's velocity to be JUM_VEL
                myPlayer.y += 1; //Make dino jump a little
                DmaChnEnable(DMA_CHANNEL2); //Play the jump audio
            }
            
            for(i = 0; i < GROUND_SIZE; i++){ //For all elements ranging in the ground array
                tft_drawFastHLine(ground[i].x, ground[i].y, ground[i].w, BG_COLOR); //Clear the old display of the ground by drawing it with black 
                ground[i].x -= SPEED; //Change the x-coordinate based on speed
                if(ground[i].x + ground[i].w <= 0){ //If the ground element is out of screen
                    ground[i].x = WIDTH; //Reset the ground element's x-coordinate
                    ground[i].y = randomRange(HEIGHT - GROUND_HEIGHT + 10, HEIGHT); //Get a new y-coordinate for the ground element
                    ground[i].w = randomRange(3, 10); //Get a new width for the ground element
                }
            }
            switch(obsType){ //Based on the value of the obstacle type
                case 0: drawBitmap(obstacle.x, (HEIGHT - GROUND_HEIGHT - ((obstacle.h / 2))), obsTypeZer, obstacle.w, obstacle.h, BG_COLOR); //For small cactus
                        break;
                case 1: drawBitmap(obstacle.x, (HEIGHT - GROUND_HEIGHT - ((obstacle.h / 2))), obsTypeOne, obstacle.w, obstacle.h, BG_COLOR); //For large cactus
                        break;
                case 2: drawBitmap(obstacle.x, (HEIGHT - GROUND_HEIGHT - ((obstacle.h / 2))), obsTypeTwo, obstacle.w, obstacle.h, BG_COLOR); //For multi cactus
                        break;
            } 
            tft_fillRect(myPlayer.x, (HEIGHT - GROUND_HEIGHT - (myPlayer.y + (myPlayer.h / 2))), myPlayer.w, myPlayer.h, BG_COLOR); //Clear the old display of the dino by drawing it with black 

            tft_drawFastHLine(0, HEIGHT - GROUND_HEIGHT, WIDTH, SOFT_COLOR); //Draw a white line to represent ground

            obstacle.x -= SPEED; //Change the x-coordinate based on speed
            if(obstacle.x + obstacle.w < 0){ //If the obstacle is out of screen
                obsType = randomRange(0, 3); //Get a new obstacle type based on random values
                obstacle.x = WIDTH + randomRange(0, 50); //Reset the x-coordinate of the obstacle to right most value with a random offset
                switch(obsType){ //Based on the value of the obstacle type
                    case 0: obstacle.w = OBS_W_0; //Set obstacle width to predefined width
                            obstacle.h = OBS_H_0; //Set obstacle height to predefined height
                            break;
                    case 1: obstacle.w = OBS_W_1; //Set obstacle width to predefined width
                            obstacle.h = OBS_H_1; //Set obstacle height to predefined height
                            break;
                    case 2: obstacle.w = OBS_W_2; //Set obstacle width to predefined width
                            obstacle.h = OBS_H_2; //Set obstacle height to predefined height
                            break;
                }
                tft_setTextColor(BG_COLOR); //Set the text color to black
                tft_setCursor(SCORE_X_OFFSET2, SCORE_Y_OFFSET1); //Set text coordinates
                sprintf(buffer, "%2d", score); //Send the score into the buffer array
                tft_writeString(buffer); //Print the text
                tft_setCursor(SCORE_X_OFFSET2, SCORE_Y_OFFSET2); //Set text coordinates
                sprintf(buffer, "%2d", highScore); //Send the high score into the buffer array
                tft_writeString(buffer); //Print the text
                score++; //Increment the score
                if(score > highScore){ //If score is greater than high score
                    highScore = score; //Update the high score
                }
                tft_setTextColor(SOFT_COLOR); //Set the text color to SOFT_COLOR
                tft_setCursor(SCORE_X_OFFSET2, SCORE_Y_OFFSET1); //Set text coordinates
                sprintf(buffer, "%2d", score); //Send the score into the buffer array
                tft_writeString(buffer); //Print the text
                tft_setCursor(SCORE_X_OFFSET2, SCORE_Y_OFFSET2); //Set text coordinates
                sprintf(buffer, "%2d", highScore); //Send the high score into the buffer array
                tft_writeString(buffer); //Print the text
            }
            if(myPlayer.y > 0){ //If the y-coordinate of the dino is greater than 0
                myPlayer.y += myPlayer.vy; //Update the y-coordinate based on velocity
                myPlayer.vy -= GRAVITY; //Update the velocity based on gravity
            }
            else if(myPlayer.y < 0){ //If the y-coordinate of the dino is less than 0
                myPlayer.y = 0; //Change the y-coordinate to 0
                myPlayer.vy = 0; //Change the velocity to 0
            }
            switch(obsType){ //Based on the value of the obstacle type
                case 0: drawBitmap(obstacle.x, (HEIGHT - GROUND_HEIGHT - ((obstacle.h / 2))), obsTypeZer, obstacle.w, obstacle.h, HARD_COLOR); //For small cactus
                        break;
                case 1: drawBitmap(obstacle.x, (HEIGHT - GROUND_HEIGHT - ((obstacle.h / 2))), obsTypeOne, obstacle.w, obstacle.h, HARD_COLOR); //For large cactus
                        break;
                case 2: drawBitmap(obstacle.x, (HEIGHT - GROUND_HEIGHT - ((obstacle.h / 2))), obsTypeTwo, obstacle.w, obstacle.h, HARD_COLOR); //For multi cactus
                        break;
            }

            for(i = 0; i < GROUND_SIZE; i++){ //For all elements ranging in the ground array
                tft_drawFastHLine(ground[i].x, ground[i].y, ground[i].w, HARD_COLOR); //Draw the new display of the ground elements
            }
            if(myPlayer.y > 0){ //If the player jumps
                drawBitmap(myPlayer.x, (HEIGHT - GROUND_HEIGHT - (myPlayer.y + (myPlayer.h / 2))), dinoJumpUp, myPlayer.w, myPlayer.h, SOFT_COLOR); //Draw the dino jump bitmap
            }
            else{
                if(runner > RUNNER_FRAMES / 2){ //If the runner frames are in the second half
                    drawBitmap(myPlayer.x, (HEIGHT - GROUND_HEIGHT - (myPlayer.y + (myPlayer.h / 2))), dinoRunOne, myPlayer.w, myPlayer.h, SOFT_COLOR); //Draw the second runner bitmap
                }
                else{ //If the runner frames are in the first half
                    drawBitmap(myPlayer.x, (HEIGHT - GROUND_HEIGHT - (myPlayer.y + (myPlayer.h / 2))), dinoRunTwo, myPlayer.w, myPlayer.h, SOFT_COLOR); //Draw the first runner bitmap
                }
            }
            runner = (runner + 1) % RUNNER_FRAMES; //Increment the runner variable
            
            if((myPlayer.x + myPlayer.w > obstacle.x) && (myPlayer.x < obstacle.x + obstacle.w) && (myPlayer.y < obstacle.h)){ //Check for collision of hitboxes
                myPlayer.alive = 0; //Set the alive flag to false
                tft_setTextSize(4); //Set the text size to 4
                tft_setTextColor(SOFT_COLOR); //Set the text color to SOFT_COLOR
                tft_setCursor(5, 60); //Set the cursor at 5, 60
                tft_writeString("!!!!!DEAD!!!!!"); //Write "!!!!!DEAD!!!!!"
                DmaChnEnable(DMA_CHANNEL3); //Play the dead audio
            }
        }
        else if(!myPlayer.alive){ //If the player is dead
            
        }
        
        exTime = 33 - (PT_GET_TIME() - begin_time); //Get remaining time to achieve 30 frames per second
        printf("%d\n", exTime); //Print out the remaining time
        PT_YIELD_TIME_msec(exTime); //Yield for the remaining time
    }
    PT_END(pt); //End the protothread
}

int main(){ //The main function
    srand(1); //Random seed
    OpenTimer2(T2_ON | T2_SOURCE_INT | T2_PS_1_1, F / Fs); //Configurations for the timer 2
    ConfigIntTimer2(T2_INT_ON | T2_INT_PRIOR_2); //Interrupt configuration on timer 2
    mT2ClearIntFlag(); //Clear the interrupt flag
    
    CloseADC10(); //Close the ADC before configuring it

	SetChanADC10(ADC_CH0_NEG_SAMPLEA_NVREF | ADC_CH0_POS_SAMPLEA_AN11);//Setup the ADC
    OpenADC10(PARAM1, PARAM2, PARAM3, PARAM4, PARAM5); //Open the ADC using above parameters
    
    EnableADC10(); //Enable the ADC
    
    OpenTimer3(T3_ON | T3_SOURCE_INT | T3_PS_1_1, 5000); //Configure timer 3
    SpiChnOpen(SPI_CHANNEL2, SPI_OPEN_ON | SPI_OPEN_MODE16 | SPI_OPEN_MSTEN | SPI_OPEN_CKE_REV | SPICON_FRMEN | SPICON_FRMPOL, SPI_CLK_DIV); //Configure SPI channel 2
    PPSOutput(2, RPB5, SDO2); //Map SPI data out to RPB5
    PPSOutput(4, RPA3, SS2); //Map SPI chip select to RPA3
    
    DmaChnOpen(DMA_CHANNEL2, 3, DMA_OPEN_DEFAULT); //Open DMA channel 2
    DmaChnSetTxfer(DMA_CHANNEL2, jumpAudio, (void*)&SPI2BUF, JUMP_AUDIO_SIZE, 2, 2); //Configure it to transmit jump audio
    DmaChnSetEventControl(DMA_CHANNEL2, DMA_EV_START_IRQ(_TIMER_3_IRQ)); //Set DMA event control
    
    DmaChnOpen(DMA_CHANNEL3, 0, DMA_OPEN_DEFAULT); //Open DMA channel 3
    DmaChnSetTxfer(DMA_CHANNEL3, deadAudio, (void*)&SPI2BUF, DEAD_AUDIO_SIZE, 2, 2); //Configure it to transmit dead audio
    DmaChnSetEventControl(DMA_CHANNEL3, DMA_EV_START_IRQ(_TIMER_3_IRQ)); //Set DMA event control
    
    int i; //Counter variable i
    for(i = 0; i < GROUND_SIZE; i++){ //For all elements ranging in the ground array
        ground[i].x = randomRange(0, WIDTH); //Assign them a random x-coordinate
        ground[i].y = randomRange(HEIGHT - GROUND_HEIGHT + 10, HEIGHT); //Assign them a random y-coordinate
        ground[i].w = randomRange(3, 10); //Assign them a random width
    }
    
    obsType = randomRange(0, 3); //Get a random obstacle type
    obstacle.x = WIDTH; //Set its x-coordinate to the right most edge
    if(obsType == 0){ //If it is obstacle type 0
        obstacle.w = OBS_W_0; //Set obstacle width to predefined width
        obstacle.h = OBS_H_0; //Set obstacle height to predefined height
    }
    else if(obsType == 1){ //If it is obstacle type 1
        obstacle.w = OBS_W_1; //Set obstacle width to predefined width
        obstacle.h = OBS_H_1; //Set obstacle height to predefined height
    }
    else{ //If it is obstacle type 2
        obstacle.w = OBS_W_2; //Set obstacle width to predefined width
        obstacle.h = OBS_H_2; //Set obstacle height to predefined height
    }
    
    myPlayer.x = 30; //Set the dino x-coordinate to be 30
    myPlayer.y = 0; //Set the dino y-coordinate to be 0
    myPlayer.w = 22; //Set the dino width to be 22
    myPlayer.h = 25; //Set the dino height to be 25
    myPlayer.vy = 0; //Set the dino velocity to be 0
    myPlayer.alive = 1; //Set the dino alive flag to be true
    
    tft_init_hw(); //Inititialise the TFT hardware
    tft_begin(); //Begin the TFT
    tft_fillScreen(BG_COLOR); //Fill the TFT screen with black colour
    tft_setRotation(1); //Set the TFT screen orientation
    
    tft_setTextSize(4); //Set text size to be 4
    tft_setTextColor(SOFT_COLOR); //Set the text color to be SOFT_COLOR
    tft_setCursor(25, 100); //Set the cursor at 25, 100
    tft_writeString("Press Start!"); //Write "Press Start!"
    
    PT_setup(); //Setup threads
    
    INTEnableSystemMultiVectoredInt(); //Enable system wide interrupts
    
    for (i = 0; i < N_WAVE; i++){ //For i raning from 0 to 512
        Sinewave[i] = float2Accum(sin(6.283 * ((float) i) / N_WAVE) * 0.5); //Setup the sinewave
        window[i] = float2Accum(1.0 - cos(6.283 * ((float) i) / (N_WAVE - 1))); //Setup the Hann window
    }
    
    pt_add(&pt_anim, 0); //Add animation thread to the chain of protothreads
    pt_add(&protothread_serial, 0); //Add serial thread to the chain of protothreads
    pt_add(&protothread_buttons, 0); //Add button thread to the chain of protothreads
    PT_INIT(&pt_sched); //Initialize the scheduler
    pt_sched_method = SCHED_ROUND_ROBIN; //Configure the scheduling method to be Round Robin 
    PT_SCHEDULE(protothread_sched(&pt_sched)); //Schedule the protothreads
}
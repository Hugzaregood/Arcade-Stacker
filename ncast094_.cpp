#include "ncast094_timerISR.h"
#include "ncast094_helper.h"
#include "ncast094_periph.h"
#include "ncast094_serialATmega.h"
#include "ncast094_LCD.h" //Using LCD cell screen libray
#include "stdio.h"
#include "ncast094_EEPROM.h" //Using EEPROM libray 
#include <math.h>

#define NUM_TASKS 7
// EEPROM Address for High Score
#define EEPROM_HIGHSCORE_ADDR 0

// Task struct for concurrent synchSMs implementations
typedef struct _task {
    signed char state;         // Task's current state
    unsigned long period;      // Task period
    unsigned long elapsedTime; // Time elapsed since last task tick
    int (*TickFct)(int);       // Task tick function
} task;

// Define Periods for each task
const unsigned long GCD_PERIOD = 10;      // Set the GCD Period
const unsigned long MATRIX_TASK_PERIOD = 100; // Update the matrix every 100 ms
const unsigned long BUTTON_START_TASK_PERIOD = 10;
const unsigned long BUTTON_STOP_TASK_PERIOD = 10;
const unsigned long SCROLLING_TASK_PERIOD = 100;
const unsigned long BUZZER_TASK_PERIOD = 10;
const unsigned long LCD_TASK_PERIOD = 10;
const unsigned long HS_TASK_PERIOD = 100;

task tasks[NUM_TASKS]; // Declared task array with 1 task

// Pin Definitions
#define CS_BIT  2 // Chip Select (PORTB2)
#define CLK_BIT 5 // SPI Clock (PORTB5)
#define DOUT_BIT 3 // SPI Data Out (PORTB3)

// States for all Tasks
enum MatrixStates { MARTIX_START, MARTIX_UPDATE };
enum ScrollingStates { SCROLL_START, SCROLL_UPDATE }; 
enum ButtonStartStates { BUTTON_START_INIT, BUTTON_START_WAIT, BUTTON_START_PRESSED };
enum ButtonStopStates { BUTTON_STOP_INIT, BUTTON_STOP_WAIT, BUTTON_STOP_PRESSED };
enum BuzzerStates { BUZZER_INIT, BUZZER_WAIT, BUZZER_PLAY, BUZZER_PLAY_BLOCK, BUZZER_PLAY_LOSER };
enum LCDStates { LCD_INIT, LCD_IDLE, LCD_WIN, LCD_LOSE, LCD_RESET, LCD_PLAY };
enum HighScoreStates { HS_INIT, HS_IDLE, HS_UPDATE, HS_DISPLAY, HS_RESET };


// SPI Initialization
void SPI_Init() {
    // Set MOSI, SCK, and CS as output
    DDRB = SetBit(DDRB, CLK_BIT, 1);   // Set CLK as output
    DDRB = SetBit(DDRB, DOUT_BIT, 1);  // Set DOUT as output
    DDRB = SetBit(DDRB, CS_BIT, 1);    // Set CS as output

    // Enable SPI, Master mode, set clock rate fosc/16
    SPCR = (1 << SPE) | (1 << MSTR) | (1 << SPR0);
}

// SPI Send Function
void SPI_Send(uint8_t data) {
    SPDR = data;                      // Load data into the SPI data register
    while (!(SPSR & (1 << SPIF)));    // Wait until transmission complete
}

// Target specific matrix and send data, with NO-OP for others
// Global flag to track SPI activity
volatile int spiInProgress = 0;

void spiTransfer(uint8_t targetMatrix, uint8_t opcode, uint8_t data, uint8_t numMatrices) { // spiTransfer(targetMatrix, rows, columns, #ofMatrices)
    // Mark SPI activity as in-progress
    spiInProgress = 1;

    // Adjust the row/column logic for a 180-degree rotated matrix
    if (opcode >= 1 && opcode <= 8) {
        opcode = 9 - opcode; // Flip rows (e.g., logical row 1 -> physical row 8)
        data = ((data & 0x01) << 7) | ((data & 0x02) << 5) | ((data & 0x04) << 3) |
               ((data & 0x08) << 1) | ((data & 0x10) >> 1) | ((data & 0x20) >> 3) |
               ((data & 0x40) >> 5) | ((data & 0x80) >> 7); // Flip columns
    }

    // Bring CS low to start transmission
    PORTB = SetBit(PORTB, CS_BIT, 0);

    for (uint8_t matrix = 0; matrix < numMatrices; matrix++) {
        if (matrix == targetMatrix) {
            // Send adjusted opcode and data to the target matrix
            SPI_Send(opcode);
            SPI_Send(data);
        } else {
            // Send NO-OP to all other matrices
            SPI_Send(0x00); // NO-OP opcode
            SPI_Send(0x00); // NO-OP data
        }
    }

    // Bring CS high to end transmission
    PORTB = SetBit(PORTB, CS_BIT, 1);

    // Mark SPI activity as complete
    spiInProgress = 0;
}


// Matrix Initialization
void Matrix_Init(uint8_t numMatrices) {
    // Initialize each matrix in the daisy chain
    for (uint8_t matrix = 0; matrix < numMatrices; matrix++) {
        // Disable test mode
        spiTransfer(matrix, 0x0F, 0x00, numMatrices);
        // Set decode mode: No decode
        spiTransfer(matrix, 0x09, 0x00, numMatrices);
        // Set brightness to maximum (0x0F)
        spiTransfer(matrix, 0x0A, 0x0F, numMatrices);
        // Set scan limit: Display all 8 rows
        spiTransfer(matrix, 0x0B, 0x07, numMatrices);
        // Exit shutdown mode: Normal operation
        spiTransfer(matrix, 0x0C, 0x01, numMatrices);
    }

    // Clear all rows in all matrices (180-degree rotation logic is in spiTransfer)
    for (uint8_t matrix = 0; matrix < numMatrices; matrix++) {
        for (uint8_t row = 1; row <= 8; row++) {
            spiTransfer(matrix, row, 0x00, numMatrices); // Clear all LEDs in the row
        }
    }
}

// Global Variables
int isScrollingActive = 1;  // Controls scrolling; disables when the game is ON
int isGameOn = 0;           // Indicates whether the game is ON
int isPlaced = 0;           // Indicates whether the block is placed
int8_t direction = -1;      // Block direction: -1 (up), 1 (down)
uint8_t currentRow = 4;     // Starting row for the block
static uint8_t isLosingSound = 0;  // Flag to indicate if loser sound is being played
static uint8_t isWinningSound = 0; // Flag to indicate if winning sound is being played
uint8_t scrollIndex = 0;              // Current scroll position
uint8_t isScrolling = 1;              // Toggle scrolling ON/OFF
uint8_t isGameStarted = 0;            // Tracks whether the game logic has started
static int isOn = 0;          // Tracks whether the LED screen is ON or OFF
static uint8_t currentScore = 0;
static uint8_t highScore = 0;
static uint8_t blockPlacedFlag = 0; // Flag to prevent double counting
uint8_t misalignment = 0; // Flag to detect misalignment


// Helper Function for Scrolling_Text
void DisplayScrollingTextVertical(uint8_t numMatrices) {
    // Define the letters "S", "T", "A", "R", "T" with additional blank rows for spacing
    uint8_t letters[6][8] = {
        {0b00000000, 0b01000110, 0b10001001, 0b10001001, 0b10010001, 0b01100010, 0b00000000, 0b00000000}, // S
        {0b00000000, 0b00000001, 0b00000001, 0b11111111, 0b00000001, 0b00000001, 0b00000000, 0b00000000}, // T
        {0b00000000, 0b11111000, 0b00010110, 0b00010011, 0b00010011, 0b00010110, 0b11111000, 0b00000000}, // A
        {0b00000000, 0b11111111, 0b00010001, 0b00010001, 0b00110001, 0b11011111, 0b00000000, 0b00000000}, // R
        {0b00000000, 0b00000001, 0b00000001, 0b11111111, 0b00000001, 0b00000001, 0b00000000, 0b00000000}, // T
        {0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000, 0b00000000}  // Blank row for spacing
    };

    static uint8_t scrollIndex = 0; // Tracks the current scroll position
    const uint8_t totalRows = 6 * 8; // Total rows (letters + spacing)

    // Clear all matrices first
    for (uint8_t matrix = 0; matrix < numMatrices; matrix++) {
        for (uint8_t row = 1; row <= 8; row++) {
            spiTransfer(matrix, row, 0x00, numMatrices); // Clear each row
        }
    }

    // Render the scrolling text frame
    for (uint8_t displayRow = 0; displayRow < numMatrices * 8; displayRow++) {
        // Calculate the source row for the current display position
        uint8_t sourceRow = (scrollIndex + displayRow) % totalRows;
        uint8_t letterIndex = sourceRow / 8; // Determine which letter or blank row
        uint8_t rowData = letters[letterIndex][sourceRow % 8]; // Get the row data

        // Determine the target matrix and row
        uint8_t targetMatrix = displayRow / 8;
        uint8_t targetRow = (displayRow % 8) + 1;

        // Display the row data on the correct matrix
        if (targetMatrix < numMatrices) {
            spiTransfer(targetMatrix, targetRow, rowData, numMatrices);
        }
    }

    // Increment scrollIndex for the next frame
    scrollIndex = (scrollIndex + 1) % totalRows;
}

// Helper Function For 
// Custom characters for smiley and frown faces
uint8_t smileyFace[8] = {
    0b00000, // Top row
    0b01010, // Eyes
    0b01010, // Eyes
    0b00000, // Space between eyes and mouth
    0b00000, // Space for mouth
    0b10001, // Corners of smile
    0b01110, // Smile curve
    0b00000  // Bottom row
};

uint8_t frownFace[8] = {
    0b00000, // Top row
    0b01010, // Eyes
    0b01010, // Eyes
    0b00000, // Space between eyes and mouth
    0b00000, // Space for mouth
    0b01110, // Frown curve
    0b10001, // Corners of frown
    0b00000  // Bottom row
};
void lcd_create_char(uint8_t location, uint8_t charmap[]) {
    location &= 0x7; // Ensure location is between 0-7
    lcd_send_command(0x40 | (location << 3)); // Set CGRAM address
    for (int i = 0; i < 8; i++) {
        lcd_write_character(charmap[i]); // Write character pattern
    }
}

////////////////////////////////// TICK FUNCTIONS /////////////////////////////////////////////

int ButtonStartTick(int state) {
    static int prevButtonState = 0; // Tracks the previous button state
    int buttonPressed = !GetBit(PINC, 0); // Read button state (active low)
    static int clearedOnce = 0; // Ensure matrices are cleared only once during transitions

    switch (state) {
        case BUTTON_START_INIT:
            state = BUTTON_START_WAIT; // Initialize to waiting state
            break;

        case BUTTON_START_WAIT:
            if (buttonPressed && !prevButtonState) { // Detect rising edge
                isOn = !isOn;        // Toggle ON/OFF state
                isScrolling = !isOn; // Stop scrolling when the game is ON

                if (isOn) {
                    // Reset the game state when turning ON
                    isPlaced = 0;
                    currentRow = 4;
                    direction = 1;

                    // Clear scrolling remnants once
                    if (!clearedOnce) {
                        for (uint8_t matrix = 0; matrix < 4; matrix++) {
                            for (uint8_t row = 1; row <= 8; row++) {
                                spiTransfer(matrix, row, 0x00, 4); // Clear all rows
                            }
                        }
                        clearedOnce = 1; // Mark as cleared
                    }
                } else {
                    // Clear all LEDs when turning OFF
                    for (uint8_t matrix = 0; matrix < 4; matrix++) {
                        for (uint8_t row = 1; row <= 8; row++) {
                            spiTransfer(matrix, row, 0x00, 4); // Clear all rows
                        }
                    }
                    clearedOnce = 0; // Reset for next transition
                }

                state = BUTTON_START_PRESSED;
            }
            break;

        case BUTTON_START_PRESSED:
            if (!buttonPressed) { // Wait for button release
                state = BUTTON_START_WAIT;
            }
            break;

        default:
            state = BUTTON_START_INIT;
            break;
    }

    prevButtonState = buttonPressed; // Update the previous button state
    return state;
}

int ButtonStopTick(int state) {
    static int prevButtonState = 0;   // Tracks the previous button state
    static int debounceLock = 0;     // Prevents rapid toggling
    int buttonPressed = GetBit(PINC, 1); // Right button state (active high)

    switch (state) {
        case BUTTON_STOP_INIT:
            debounceLock = 0;         // Reset debounce lock
            state = BUTTON_STOP_WAIT; // Initialize to waiting state
            break;

        case BUTTON_STOP_WAIT:
            if (!debounceLock && buttonPressed && !prevButtonState) { // Detect rising edge
                isPlaced = !isPlaced;  // Toggle placement state
                debounceLock = 1;      // Lock debounce for 50ms
                state = BUTTON_STOP_PRESSED;
            }
            break;

        case BUTTON_STOP_PRESSED:
            if (!buttonPressed) {      // Wait for button release
                state = BUTTON_STOP_WAIT;
                debounceLock = 0;      // Release debounce lock
            }
            break;

        default:
            state = BUTTON_STOP_INIT;
            break;
    }

    prevButtonState = buttonPressed; // Update the previous button state
    return state;
}

int MatrixControlTick(int state) {
    static uint8_t currentRow = 1;       // Start at the leftmost column (column 1)
    static int8_t direction = 1;        // 1 = moving right, -1 = moving left
    static uint8_t stackColumn = 0xC0;  // Initial column pattern for the block
    static uint8_t placedBlocks[8][4] = {{0}}; // Tracks rows with placed blocks for all 4 matrices
    static uint8_t currentMatrix = 3;   // Start at the bottommost matrix
    const uint8_t numRows = 8;          // Total number of rows in a matrix
    uint8_t blockRows = 3;              // Height of the 3x2 block
    static uint8_t placedCount = 0;     // Count of placed blocks in the current stack
    static uint8_t transitionInProgress = 0; // Prevents automatic placement during transitions
    static uint8_t isFirstBlock = 1;    // Tracks if it's the first block being placed
    static uint8_t activeRows[3] = {0}; // Tracks active rows of the last placed block

    switch (state) {
        case MARTIX_START:
            state = MARTIX_UPDATE;
            break;

        case MARTIX_UPDATE:
            if (isOn) { // Game is ON
                // Adjust blockRows based on currentMatrix
                if (currentMatrix == 1) {
                    blockRows = 2; // Subtract 1 for matrix 2
                } else if (currentMatrix == 0) {
                    blockRows = 1; // Subtract 2 for matrix 3
                } else {
                    blockRows = 3; // Default for other matrices
                }
                if (!isPlaced && !transitionInProgress) { // Move the block if it's not placed and no transition
                    for (uint8_t row = 1; row <= numRows; row++) {
                        uint8_t combinedRow = placedBlocks[row - 1][currentMatrix]; // Keep placed blocks
                        if (row >= currentRow && row < currentRow + blockRows) {
                            combinedRow |= stackColumn; // Add the moving block
                        }
                        spiTransfer(currentMatrix, row, combinedRow, 4); // Update the row
                    }

                    // Update block's horizontal position
                    currentRow += direction;

                    // Check for boundary collisions
                    if (currentRow == 1 || currentRow + blockRows - 1 >= numRows) {
                        direction = -direction; // Reverse direction at the edges
                    }
                } else if (isPlaced && !blockPlacedFlag && !transitionInProgress) { // If the block is placed
                    misalignment = 0;

                    if (!isFirstBlock) {
                        // Check alignment with the rows of the last block
                        for (uint8_t i = 0; i < blockRows; i++) {
                            uint8_t targetRow = currentRow + i - 1; // Row index for placedBlocks
                            if (targetRow < numRows) {
                                // Compare the target row with the corresponding active row
                                if (targetRow != activeRows[i]) {
                                    misalignment = 1; // Rows don't align
                                    break;
                                }
                            }
                        }
                    } else {
                        // Free points for placing the first block
                        isFirstBlock = 0; // First block is valid by default
                    }

                    if (misalignment) {
                        // If misalignment is detected, reset the game
                        isOn = 0; // Turn off the game
                        isWinningSound = 0; // Ensure winning sound does not play
                        for (uint8_t matrix = 0; matrix < 4; matrix++) {
                            for (uint8_t row = 1; row <= numRows; row++) {
                                spiTransfer(matrix, row, 0x00, 4); // Clear all rows
                            }
                        }

                        // Clear the placedBlocks array manually
                        for (uint8_t row = 0; row < numRows; row++) {
                            for (uint8_t matrix = 0; matrix < 4; matrix++) {
                                placedBlocks[row][matrix] = 0;
                            }
                        }

                        currentMatrix = 3; // Reset to the bottommost matrix
                        // currentScore = 0; //Reset Score
                        stackColumn = 0xC0; // Reset column pattern
                        currentRow = 1;     // Reset column position
                        direction = 1;      // Reset direction
                        placedCount = 0;    // Reset placed count
                        isPlaced = 0;       // Reset placement flag
                        isFirstBlock = 1;   // Reset first block flag
                        isLosingSound = 1;  // Loser flag
                        transitionInProgress = 0; // Reset transition flag
                        break; // Exit early after resetting
                    }

                    // Freeze the block visually and update placedBlocks
                    for (uint8_t i = 0; i < blockRows; i++) {
                        uint8_t targetRow = currentRow + i - 1;
                        if (targetRow < numRows) {
                            placedBlocks[targetRow][currentMatrix] |= stackColumn;
                            activeRows[i] = targetRow; // Update the active rows for the next block
                        }
                    }

                    for (uint8_t row = 1; row <= numRows; row++) {
                        spiTransfer(currentMatrix, row, placedBlocks[row - 1][currentMatrix], 4);
                    }

                    // Increment the placed block count
                    placedCount++;

                    if (placedCount == 4) {
                        // Transition to next matrix
                        stackColumn = 0xC0;   
                        placedCount = 0;     
                        transitionInProgress = 1; 

                        if (currentMatrix > 0) {
                            currentMatrix--; 
                        } else {
                            // Player wins the game
                            isWinningSound = 1; // Trigger the winning sound
                            for (uint8_t matrix = 0; matrix < 4; matrix++) {
                                for (uint8_t row = 1; row <= numRows; row++) {
                                    spiTransfer(matrix, row, 0x00, 4); // Clear all rows
                                }
                            }

                            // Clear the placedBlocks array manually
                            for (uint8_t row = 0; row < numRows; row++) {
                                for (uint8_t matrix = 0; matrix < 4; matrix++) {
                                    placedBlocks[row][matrix] = 0;
                                }
                            }

                            currentMatrix = 3; 
                            // currentScore = 0; //Reset Score
                            stackColumn = 0xC0; 
                            currentRow = 1;     
                            direction = 1;     
                            placedCount = 0;    
                            isPlaced = 0;       
                            isFirstBlock = 1;   
                            transitionInProgress = 0; 
                            isOn = 0; // Turn off the game
                        }
                    } else {
                        stackColumn >>= 2; 
                        currentRow = 1;   
                        direction = 1;    
                        isPlaced = 0;     
                    }
                } else if (transitionInProgress) {
                    transitionInProgress = 0; 
                    isPlaced = 0;  
                }
            } else {
                // Clear game state when turned OFF
                currentMatrix = 3; 
                stackColumn = 0xC0; 
                currentScore = 0; //Reset Score
                currentRow = 1;     
                direction = 1;     
                placedCount = 0;    
                isPlaced = 0;       
                isFirstBlock = 1;   
                transitionInProgress = 0;

                for (uint8_t matrix = 0; matrix < 4; matrix++) {
                    for (uint8_t row = 1; row <= numRows; row++) {
                        spiTransfer(matrix, row, 0x00, 4); 
                    }
                }

                for (uint8_t row = 0; row < numRows; row++) {
                    for (uint8_t matrix = 0; matrix < 4; matrix++) {
                        placedBlocks[row][matrix] = 0;
                    }
                }
            }
            break;

        default:
            state = MARTIX_START;
            break;
    }

    return state;
}

int ScrollingTick(int state) {
    static uint8_t scrollIndex = 0; // Tracks the current scroll position
    static int clearedOnce = 0;    // Ensure scrolling clear happens once

    switch (state) {
        case SCROLL_START:
            state = SCROLL_UPDATE;
            break;

        case SCROLL_UPDATE:
            if (isOn) {
                // If the game is ON, stop scrolling and clear all matrices once
                if (!clearedOnce) {
                    for (uint8_t matrix = 0; matrix < 4; matrix++) {
                        for (uint8_t row = 1; row <= 8; row++) {
                            spiTransfer(matrix, row, 0x00, 4); // Clear all rows
                        }
                    }
                    clearedOnce = 1; // Mark as cleared
                }
            } else if (isScrolling) {
                // Render the scrolling frame only when scrolling is active
                DisplayScrollingTextVertical(4);
                scrollIndex = (scrollIndex + 1) % (6 * 8); // Wrap around scroll index
                clearedOnce = 0; // Allow clearing again when scrolling stops
            }
            break;

        default:
            state = SCROLL_START;
            break;
    }

    return state;
}

int BuzzerTick(int state) {
    static uint16_t buzzerCounter = 0; // Counter for note duration
    static uint8_t noteIndex = 0;     // Current note in the melody
    static uint8_t songPlaying = 0;   // Flag for song in progress
    static uint8_t blockSoundPlaying = 0; // Flag for block-placing sound in progress

    // Winning sound (Ascending tones) 
    const uint16_t noteFrequenciesWinning[] = {2441, 1922, 1610, 1204}; // C, E, G, High C (ICR1 values)
    const uint16_t noteDurationsWinning[] = {25, 25, 25, 100};          // Short, short, short, long

    // Loser sound (descending tones) will most likely change
    const uint16_t noteFrequenciesLosing[] = {3300, 3600, 3800, 4000}; // Lower-pitched notes
    const uint16_t noteDurationsLosing[] = {50, 50, 50, 100};           // Equal duration

    // Block-placing sound (short alternating tones for variety)
    const uint16_t noteFrequenciesBlock[] = {2000, 1600}; // Two tones for placing a block
    const uint16_t noteDurationsBlock[] = {25, 25};       // Equal duration for both tones

    switch (state) {
        case BUZZER_INIT:
            if (isWinningSound) { // Start the winning sound sequence
                buzzerCounter = noteDurationsWinning[noteIndex];
                ICR1 = noteFrequenciesWinning[noteIndex]; // Set frequency for the current note
                OCR1A = ICR1 / 2;                        // 50% duty cycle
                TCCR1A = (1 << COM1A1) | (1 << WGM11);   // Fast PWM, non-inverting
                TCCR1B = (1 << WGM12) | (1 << WGM13) | (1 << CS11); // Fast PWM, prescaler 8
                songPlaying = 1;
                state = BUZZER_PLAY;
            } else if (isLosingSound) { // Start the loser sound sequence
                buzzerCounter = noteDurationsLosing[noteIndex];
                ICR1 = noteFrequenciesLosing[noteIndex]; // Set frequency for the current note
                OCR1A = ICR1 / 2;                        // 50% duty cycle
                TCCR1A = (1 << COM1A1) | (1 << WGM11);   // Fast PWM, non-inverting
                TCCR1B = (1 << WGM12) | (1 << WGM13) | (1 << CS11); // Fast PWM, prescaler 8
                songPlaying = 1;
                state = BUZZER_PLAY_LOSER;
            } else if (isPlaced && isOn && !blockSoundPlaying) { // Start the block-placing sound only if the game is ON
                buzzerCounter = noteDurationsBlock[0];
                ICR1 = noteFrequenciesBlock[0]; // Set frequency for the first block tone
                OCR1A = ICR1 / 2;               // 50% duty cycle
                TCCR1A = (1 << COM1A1) | (1 << WGM11);   // Fast PWM, non-inverting
                TCCR1B = (1 << WGM12) | (1 << WGM13) | (1 << CS11); // Fast PWM, prescaler 8
                blockSoundPlaying = 1;
                state = BUZZER_PLAY_BLOCK;
            } else {
                OCR1A = 0; // Turn off PWM output
                TCCR1A = 0;
                TCCR1B = 0;
                songPlaying = 0;
                blockSoundPlaying = 0;
                state = BUZZER_WAIT;
            }
            break;

        case BUZZER_PLAY:
            if (buzzerCounter > 0) {
                buzzerCounter--;
            } else {
                // Move to the next note for the winning sound
                noteIndex++;
                if (noteIndex < 4) { // Play next note if available
                    buzzerCounter = noteDurationsWinning[noteIndex];
                    ICR1 = noteFrequenciesWinning[noteIndex];
                    OCR1A = ICR1 / 2; // 50% duty cycle
                } else { // End of the melody
                    isWinningSound = 0; // Reset the winning sound flag
                    noteIndex = 0;      // Reset the note index
                    OCR1A = 0;          // Disable PWM
                    TCCR1A = 0;
                    TCCR1B = 0;
                    songPlaying = 0;
                    state = BUZZER_WAIT;
                }
            }
            break;

        case BUZZER_PLAY_LOSER:
            if (buzzerCounter > 0) {
                buzzerCounter--;
            } else {
                // Move to the next note for the loser sound
                noteIndex++;
                if (noteIndex < 4) { // Play next note if available
                    buzzerCounter = noteDurationsLosing[noteIndex];
                    ICR1 = noteFrequenciesLosing[noteIndex];
                    OCR1A = ICR1 / 2; // 50% duty cycle
                } else { // End of the melody
                    isLosingSound = 0; // Reset the losing sound flag
                    noteIndex = 0;     // Reset the note index
                    OCR1A = 0;         // Disable PWM
                    TCCR1A = 0;
                    TCCR1B = 0;
                    songPlaying = 0;
                    state = BUZZER_WAIT;
                }
            }
            break;

        case BUZZER_PLAY_BLOCK:
            if (buzzerCounter > 0) {
                buzzerCounter--;
            } else {
                // Alternate between block tones
                static uint8_t blockToneIndex = 0; // Track current block tone
                blockToneIndex = (blockToneIndex + 1) % 2; // Alternate tones

                if (blockToneIndex == 0) { // End the block sound after one cycle
                    isPlaced = 0; // Reset block-placing flag
                    blockSoundPlaying = 0;
                    OCR1A = 0; // Turn off PWM
                    TCCR1A = 0;
                    TCCR1B = 0;
                    state = BUZZER_WAIT;
                } else { // Continue the block sound
                    buzzerCounter = noteDurationsBlock[blockToneIndex];
                    ICR1 = noteFrequenciesBlock[blockToneIndex];
                    OCR1A = ICR1 / 2; // 50% duty cycle
                }
            }
            break;

        case BUZZER_WAIT:
            if (isWinningSound && !songPlaying) { // Restart the winning sound if triggered again
                noteIndex = 0;
                buzzerCounter = noteDurationsWinning[noteIndex];
                ICR1 = noteFrequenciesWinning[noteIndex];
                OCR1A = ICR1 / 2;                        // 50% duty cycle
                TCCR1A = (1 << COM1A1) | (1 << WGM11);   // Fast PWM
                TCCR1B = (1 << WGM12) | (1 << WGM13) | (1 << CS11); // Prescaler 8
                songPlaying = 1;
                state = BUZZER_PLAY;
            } else if (isLosingSound && !songPlaying) { // Restart the loser sound if triggered again
                noteIndex = 0;
                buzzerCounter = noteDurationsLosing[noteIndex];
                ICR1 = noteFrequenciesLosing[noteIndex];
                OCR1A = ICR1 / 2;                        // 50% duty cycle
                TCCR1A = (1 << COM1A1) | (1 << WGM11);   // Fast PWM
                TCCR1B = (1 << WGM12) | (1 << WGM13) | (1 << CS11); // Prescaler 8
                songPlaying = 1;
                state = BUZZER_PLAY_LOSER;
            } else if (isPlaced && isOn && !blockSoundPlaying) { // Start the block-placing sound if triggered again and game is ON
                buzzerCounter = noteDurationsBlock[0];
                ICR1 = noteFrequenciesBlock[0];
                OCR1A = ICR1 / 2;                        // 50% duty cycle
                TCCR1A = (1 << COM1A1) | (1 << WGM11);   // Fast PWM
                TCCR1B = (1 << WGM12) | (1 << WGM13) | (1 << CS11); // Fast PWM
                blockSoundPlaying = 1;
                state = BUZZER_PLAY_BLOCK;
            }
            break;

        default:
            state = BUZZER_INIT;
            break;
    }

    return state;
}


int LCDTick(int state) {
    static uint8_t lcdInitialized = 0; // Track if LCD is initialized
    static int lastState = LCD_IDLE;   // Track the last processed state to avoid redundant updates

    switch (state) {
        case LCD_INIT:
            if (!lcdInitialized) {
                lcd_create_char(0, smileyFace); // Create smiley face at location 0
                lcd_create_char(1, frownFace);  // Create frown face at location 1
                lcd_clear();
                lcd_write_str((char*) "Game Ready!");
                lcd_goto_xy(1, 0);
                lcd_write_str((char*) "Press Start!");
                lcdInitialized = 1; // Mark initialization as done
            }
            state = LCD_IDLE;
            lastState = LCD_INIT;
            break;

        case LCD_IDLE:
            if (isOn && lastState != LCD_PLAY) {
                state = LCD_PLAY;
            } else if (isWinningSound && lastState != LCD_WIN) {
                state = LCD_WIN;
            } else if (isLosingSound && lastState != LCD_LOSE) {
                state = LCD_LOSE;
            }
            break;

        case LCD_PLAY:
            if (lastState != LCD_PLAY) {
                lcd_clear();
                lcd_write_str((char*) "Game On!");
                lcd_goto_xy(1, 0);
                lcd_write_str((char*) "Good Luck!");
                lastState = LCD_PLAY; // Update last state
            }
            if (isWinningSound) {
                state = LCD_WIN;
            } else if (isLosingSound) {
                state = LCD_LOSE;
            } else if (!isOn) {
                state = LCD_RESET;
            }
            break;

        case LCD_WIN:
            if (lastState != LCD_WIN) {
                lcd_clear();
                lcd_write_str((char*) "You Win!");
                lcd_goto_xy(1, 0);
                lcd_write_character(0); // Display smiley face

                // Display the high score on the bottom far right
                char highScoreStr[10];
                sprintf(highScoreStr, "High:%d", highScore); // Format high score string
                lcd_goto_xy(1, 8); // Place it on the far right of the second row
                lcd_write_str(highScoreStr);

                lastState = LCD_WIN;    // Update last state
            }
            state = LCD_IDLE;
            break;

        case LCD_LOSE:
            if (lastState != LCD_LOSE) {
                lcd_clear();
                lcd_write_str((char*) "You Lose!");
                lcd_goto_xy(1, 0);
                lcd_write_character(1); // Display frown face

                // Display the high score on the bottom far right
                char highScoreStr[10];
                sprintf(highScoreStr, "High:%d", highScore); // Format high score string
                lcd_goto_xy(1, 8); // Place it on the far right of the second row
                lcd_write_str(highScoreStr);

                lastState = LCD_LOSE;   // Update last state
            }
            state = LCD_IDLE;
            break;

        case LCD_RESET:
            if (lastState != LCD_RESET) {
                lcd_clear();
                lcd_write_str((char*) "Game Reset");
                lcd_goto_xy(1, 0);
                lcd_write_str((char*) "Press Start!");
                lastState = LCD_RESET; // Update last state
            }
            state = LCD_IDLE;
            break;

        default:
            state = LCD_INIT;
            lastState = LCD_INIT;
            break;
    }

    return state;
}


int HighScoreTick(int state) {
    switch (state) {
        case HS_INIT:
            // Read the high score from EEPROM during initialization
            // EEPROM.write(EEPROM_HIGHSCORE_ADDR, 0); // Reseting Score/data on EEPROM (Just for debugging)
            highScore = EEPROM.read(EEPROM_HIGHSCORE_ADDR);
            state = HS_IDLE;
            break;

        case HS_IDLE:
            // serial_println(currentScore);
            if (GetBit(PINC, 1) && !misalignment && isOn) {
                // Increment the current score by 10 for each block placement
                serial_println(currentScore);
                currentScore += 10;
                state = HS_UPDATE;
            } else if (isLosingSound) {
                // Check for high score and update EEPROM
                if (currentScore > highScore) {
                    highScore = currentScore;
                    EEPROM.write(EEPROM_HIGHSCORE_ADDR, highScore); // Save to EEPROM
                }
                state = HS_IDLE;
            }
            else if (isWinningSound) {
            // GIVE MAX POINTS
                highScore = 160;
                EEPROM.write(EEPROM_HIGHSCORE_ADDR, highScore); // Save to EEPROM
                state = HS_IDLE;
            }
            break;

        // case HS_UPDATE:
        //     // High score update logic handled in HS_IDLE
        //     state = HS_IDLE;
        //     break;

        case HS_RESET:
            // Reset the current score when the game is restarted
            currentScore = 0;
            state = HS_IDLE;
            break;

        default:
            state = HS_INIT;
            break;
    }

    return state;
}



void TimerISR() {
    for (unsigned int i = 0; i < NUM_TASKS; i++) {                   // Iterate through each task in the task array
        if (tasks[i].elapsedTime >= tasks[i].period) {               // Check if the task is ready to tick
            tasks[i].state = tasks[i].TickFct(tasks[i].state);       // Tick and set the next state for this task
            tasks[i].elapsedTime = 0;                                // Reset the elapsed time for the next tick
        }
        tasks[i].elapsedTime += GCD_PERIOD;                          // Increment the elapsed time by GCD_PERIOD
    }
}

int main(void) {
    // Initialize SPI
    serial_init(9600);
    SPI_Init();
    lcd_init();

    DDRB = 0b101111;

    // Initialize LED matrix (4 matrices in the chain)
    Matrix_Init(4);

    // Initialize tasks

    tasks[0].state = BUTTON_START_INIT;
    tasks[0].period = BUTTON_START_TASK_PERIOD;
    tasks[0].elapsedTime = 0;
    tasks[0].TickFct = &ButtonStartTick;

    tasks[1].state = BUTTON_STOP_INIT;
    tasks[1].period = BUTTON_STOP_TASK_PERIOD;
    tasks[1].elapsedTime = 0;
    tasks[1].TickFct = &ButtonStopTick;

    tasks[2].state = MARTIX_START;
    tasks[2].period = MATRIX_TASK_PERIOD;
    tasks[2].elapsedTime = 0;
    tasks[2].TickFct = &MatrixControlTick;

    tasks[3].state = SCROLL_START;
    tasks[3].period = SCROLLING_TASK_PERIOD;
    tasks[3].elapsedTime = 0;
    tasks[3].TickFct = &ScrollingTick;

    tasks[4].state = BUZZER_INIT;
    tasks[4].period = BUZZER_TASK_PERIOD; 
    tasks[4].elapsedTime = 0;
    tasks[4].TickFct = &BuzzerTick;

    tasks[5].state = LCD_INIT;
    tasks[5].period = LCD_TASK_PERIOD; 
    tasks[5].elapsedTime = 0;
    tasks[5].TickFct = &LCDTick;

    tasks[6].state = HS_INIT;
    tasks[6].period = HS_TASK_PERIOD; 
    tasks[6].elapsedTime = 0;
    tasks[6].TickFct = &HighScoreTick;

    // Set Timer
    TimerSet(GCD_PERIOD);
    TimerOn();

    while (1) {
        // Main loop, TimerISR handles tasks
    }

    return 0;
}

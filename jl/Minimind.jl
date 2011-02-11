public class Mastermind 
{
    int{Bob:}[]{Bob:} code;                // bob's secret code
    int numGuesses = 0;                    // the number of guesses Alice has made
    
    // some enums to specify the response to Alice's guess
    final int NOT_CORRECT = 0;
    final int CORRECT_COLOR = 1; 
    final int CORRECT_COLOR_AND_POSITION = 2; 
    int{}[]{} returnArray;
    
    public void miniguess{}(int{}[]{} aliceGuess) {
	// return an array to Alice with information on Alice's guesses 

	int j = 0;
	while(j < code.length) {  
	    //returnArray[j] = code[j];
	    j = j + 1;
	}
	returnArray[0] = j;
    }
}
public class Bork {

    int{Alice:}[]{Alice:} code;
    int{}[]{} aliceGuess;
    int{}[]{} returnArray;

    final int CORRECT_COLOR = 1; 
    final int CORRECT_COLOR_AND_POSITION = 2; 

    public void foo{}() { 
	for(int j = 0; j < code.length; ++j) {  
	    
	    int guessResult;
	    if (code[j] == 0) {
		guessResult = 1;
	    }
	    else if (code[j] == 1) {
		guessResult = 0;
	    }

	    if (guessResult != -1) {
		returnArray[0] = guessResult;
	    }
	} 
    }

}
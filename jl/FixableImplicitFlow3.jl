public class FixableImplicitFlow {

    int{Alice:} aliceInt;
    int{} bobInt;

    public void test{}() {
	int temp;
	int bork;
	
	if (aliceInt == 0) {
	    if (aliceInt == 3) {
		temp = 1;
	    }
	    else { 
		temp = 2;
	    }
	}

	bobInt = temp;
    }
}
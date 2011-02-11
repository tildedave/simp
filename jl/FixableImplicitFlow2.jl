public class FixableImplicitFlow {

    int{Alice:} aliceInt;
    int{} bobInt;

    public void test{}() {
	if (aliceInt == 3) {
	    bork(2);
	}
    }

    public void bork{}(int k) {
    }

}
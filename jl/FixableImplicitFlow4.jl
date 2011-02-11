public class FixableImplicitFlow {

    int{Alice:} aliceInt;
    int{} bobInt;

    public void test{Alice:}() {
	if (aliceInt == 3) {
	    bobInt = 2;
	}
    }

}
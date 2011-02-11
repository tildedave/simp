public class FixableMultipleFixes {

    int{Alice:} aliceInt;
    int{} publicInt;

    public void test{}() {
	int k = aliceInt;
	int y = k;
	int b = y;

	publicInt = b;
    }


}
public class IllegalArrayCall2 {

    int{Alice:}[]{Alice:} aliceArray;
    int{}[]{} bobArray;

    public void test{}() {
	while (aliceArray.length < 0) {
	    bobArray[0] = (aliceArray[0] * 2);
	}
    }


}
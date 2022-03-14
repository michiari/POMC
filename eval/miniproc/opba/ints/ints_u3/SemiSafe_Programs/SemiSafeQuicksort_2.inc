/*  Corresponding Procedure in Java syntax:

	main(){
		try{
			qs();
		}catch(){
			parseList();
			// null elements removed
			qs();
		}
	}

	//same procedure as in Correct Quicksort
	qs(){
		... 
		accessValues();
		...
	}

	parseList(){
		hasParsed = true;
	}

	accessValues(){
		if(*){
			throw();
		} else{
			\\ readValues
		}
	}
*/

program:
bool  okay, hasParsed;
s3 left, right, lo, hi, eq;
u3 piv, swapLeft, swapRight, tmp;
u3[2] a;

main() {
	left = 0s3;
	right = 1s3;
	a[0s3] = *;
	a[1s3] = *;
	hasParsed = false;
	try {
	 	qs();
	} catch {
		hasParsed = true;
		left = 0s3;
		right = 1s3;
		qs();
	}
}

qs() {
	if (left >= right) {
	} else {
		piv = a[right]; 
		eq = left;
		lo = eq;
		hi = right;
		while (lo <= hi) { 
			if (a[hi] > piv){
				hi = hi - 1s3; 
			} else {
				swapLeft = lo;
				swapRight = hi;
				swapElements();
				if (a[lo] < piv){
					swapLeft = lo;
					swapRight = eq;
					swapElements();
					eq = eq + 1s3;
				} else {}
				lo = lo + 1s3;
			}
		}

		// recursive calls
		if (lo == 0s3 && right == 1s3){
			qsRec0();
		} else {
			qsRec1();
		}
	}
}

swapElements() {
	accessValues();
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
	okay = a[0s3] <= a[1s3];
}

accessValues(){
	if (*){
		throw;
	} else {}
}

//recursive cases depending on the value of lo for a two-elements array
qsRec0() {
	left = 0s3;
	right = eq - 1s3;
	qs();
	lo = 0s3; 
	right = 1s3;
	qs();
}

qsRec1() {
	left = 0s3;
	right = eq - 1s3;
	qs();
	//abort second recursive call, it involves at most one element
	//qs();
}
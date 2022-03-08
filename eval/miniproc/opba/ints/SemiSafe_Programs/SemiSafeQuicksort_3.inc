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
u* piv, swapLeft, swapRight, tmp;
u*[3] a;

main() {
	left = 0s4;
	right = 2s4;
	a[0s4] = *;
	a[1s4] = *;
	a[2s4] = *;
	hasParsed = false;
	try {
	 	qs();
	} catch {
		hasParsed = true;
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
			qsif();
		}

		// recursive calls
		if (lo == 0s4 && right == 1s4){
			qsRec0();
		} else {
			if (lo == 0s4 && right == 2s4){
				qsRec1();
			} else {
				if (lo == 1s4 && right == 2s4){
					qsRec2();
				} else {
					qsRec3();
				}
			} 
		}
	}
}

qsif() { 
	if (a[hi] > piv){
		hi = hi - 1s4; 
	} else {
		swapLeft = lo;
		swapRight = hi;
		swapElements();
		if (a[lo] < piv){
			swapLeft = lo;
			swapRight = eq;
			swapElements();
		} else {}
		lo = lo + 1s4;
	}
}

swapElements() {
	accessValues();
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
	okay = a[0s4] <= a[1s4] && a[1s4] <= a[2s4];
}

accessValues(){
	if (*){
		throw;
	} else {}
}

//recursive cases depending on the value of lo and right for a three-elements array
qsRec0() {
	left = 0s4;
	right = eq - 1s4;
	qs();
	left = 0s4; 
	right = 1s4;
	qs();
}

qsRec1() {
	left = 0s4;
	right = eq - 1s4;
	qs();
	left = 0s4; 
	right = 2s4;
	qs();
}

qsRec2() {
	left = 0s4;
	right = eq - 1s4;
	qs();
	left = 1s4; 
	right = 2s4;
	qs();
}

qsRec3() {
	left = 0s4;
	right = eq - 1s4;
	qs();
	//abort second recursive call, it involves at most one element
	//qs();
}
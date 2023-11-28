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
		...
		hasParsed = true;
	}

	accessValues(){
		if(*){
			throw();
		} else{
			// readValues
		}
	}
*/

program:
bool sorted, hasParsed;
u*[2] a;

main() {
	a[0s3] = *;
	a[1s3] = *;
	hasParsed = false;
	try {
	 	qs(0s3, 1s3);
	} catch {
		hasParsed = true;
		//qs(0s3, 1s3);
	}
}

qs(s3 left, s3 right) {
	s3 lo, hi, eq;
	u* piv;

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
				swapElements(lo, hi);
				if (a[lo] < piv){
					swapElements(lo, eq);
					eq = eq + 1s3;
				} else {}
				lo = lo + 1s3;
			}
		}
		qs(left,eq-1s3);
		qs(lo,right);
	}
}

swapElements(s3 swapLeft, s3 swapRight) {
    u* tmp;
    
    accessValues();
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
	sorted = a[0s3] <= a[1s3];
}

accessValues(){
	if (*){
		throw;
	} else {}
}

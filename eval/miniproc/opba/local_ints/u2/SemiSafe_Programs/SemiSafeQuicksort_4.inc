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
u2[4] a;

main() {
	a[0s4] = *;
	a[1s4] = *;
	a[2s4] = *;
	a[3s4] = *;
	hasParsed = false;
	try {
	 	qs(0s4, 3s4);
	} catch {
		hasParsed = true;
		left = 0s4;
		right = 3s4;
		qs(0s4, 3s4);
	}
}

qs(s4 left, s4 right) {
	s4 lo, hi, eq;
	u2 piv;

	if (left >= right) {
	} else {
		piv = a[right]; 
		eq = left;
		lo = eq;
		hi = right;
		while (lo <= hi) { 
			if (a[hi] > piv){
				hi = hi - 1s4; 
			} else {
				swapElements(lo, hi);
				if (a[lo] < piv){
					swapElements(lo, eq);
					eq = eq + 1s4;
				} else {}
				lo = lo + 1s4;
			}
		}
		qs(left,eq-1s4);
		qs(lo,right);	
	}
}

swapElements(s4 swapLeft, s4 swapRight) {
    u2 tmp;
    
    accessValues();
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
	sorted = a[0s4] <= a[1s4] && a[1s4] <= a[2s4] && a[2s4] <= a[3s4];
}

accessValues(){
	if (*){
		throw;
	} else {}
}

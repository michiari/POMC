/*  Corresponding Procedure in Java syntax:
	static int stackCounter;
	static int MAX;

	main(){
		stackCounter = 0;
		while(true){
			// a = generate array to sort
			try{
				qs(a);
			}catch(){
				// signal error
			}
		}
	}

	//Correct Quicksort procedure
	qs(){
		pushCounter();
		... 
		...
		popCounter();
	}

	pushCounter(){
		if (stackCounter == MAX){
			throw();
		} else {
			stackCounter++;
		}
	}

	popCounter(){
		stackCounter--;
	}
*/

program:
u2 stackCounter;
u2 MAX = 3u2;
bool sorted;
u*[2] a;

main() {
	stackCounter = 0u2;
	while(true) {
		a[0s3] = *;
		a[1s3] = *;
		try {
		 	qs(0s3, 1s3);
		} catch {
		}
	}
}

qs(s3 left, s3 right) {
	pushCounter();
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
	popCounter();
}

swapElements(s3 swapLeft, s3 swapRight) {
    u* tmp;
    
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
	sorted = a[0s3] <= a[1s3];
}

pushCounter() {
	if (stackCounter == MAX) {
		throw();
	} else {
		stackCounter = stackCounter + 1u2;
	}
}

popCounter() {
	stackCounter = stackCounter - 1u2;
}
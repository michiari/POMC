/*  Corresponding Procedure in Java syntax:
	static int stackCounter;
	static int MAX_STACK;

	main(){
		while(true){
			// a = generate array to sort
			stackCounter = 0;
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
		if (stackCounter == MAX_STACK){
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
u2 stackCounter, MAX_STACK;
bool sorted, maxReached;
u*[2] a;

main() {
	MAX_STACK = 3u2;
	while(true) {
		a[0s3] = *;
		a[1s3] = *;
		stackCounter = 0u2;
		sorted = a[0s3] <= a[1s3];
		maxReached = false;
		try {
		 	qs(0s3, 1s3);
		} catch {
		}
	}
}

qs(s3 left, s3 right) {
	s3 lo, hi, eq;
	u* piv;

	pushCounter();
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
	if (stackCounter == MAX_STACK) {
		maxReached = true;
		throw;
	} else {
		stackCounter = stackCounter + 1u2;
	}
}

popCounter() {
	stackCounter = stackCounter - 1u2;
}
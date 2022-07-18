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
u2[4] a;

main() {
	stackCounter = 0u2;
	while(true) {
		a[0s4] = *;
		a[1s4] = *;
		a[2s4] = *;
		a[3s4] = *;
		try {
		 	qs(0s4, 3s4);
		} catch {
		}
	}
}

qs(s4 left, s4 right) {
	pushCounter();
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
	popCounter();
}

swapElements(s4 swapLeft, s4 swapRight) {
    u2 tmp;
    
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
	sorted = a[0s4] <= a[1s4] && a[1s4] <= a[2s4] && a[2s4] <= a[3s4];
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
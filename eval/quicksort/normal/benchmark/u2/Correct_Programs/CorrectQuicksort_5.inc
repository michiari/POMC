/*  Corresponding procedure in C syntax:

	void quicksort (int left,int right)
	{
		int lo,eq,hi,piv;
		if (left >= right) return;
		piv = a[right]; lo = eq = left; hi = right;
		while (lo <= hi) {
			if (a[hi] > piv) {
				hi--;
			} else {
				swap a[lo],a[hi];
				if (a[lo] < piv) {
					swap a[lo],a[eq];
					eq++;
				}
				lo++;
			}
		}
		quicksort(left,eq-1);
		quicksort(lo,right);
	}

	Ref: Schwoon, Stefan. Model-checking pushdown systems. Diss. Technische Universität München, 2002. 
*/			

program:
bool sorted;
u2[5] a;

main() {
	a[0s4] = *;
	a[1s4] = *;
	a[2s4] = *;
	a[3s4] = *;
	a[4s4] = *;
	qs(0s4, 4s4);
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
    
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
	sorted = a[0s4] <= a[1s4] && a[1s4] <= a[2s4] && a[2s4] <= a[3s4] && a[3s4] <= a[4s4];
}


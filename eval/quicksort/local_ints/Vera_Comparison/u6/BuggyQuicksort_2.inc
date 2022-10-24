/*  Corresponding procedure in C syntax:

	void quicksort (int left,int right)
	{
		int lo,hi,piv;
		if (left >= right) return;
		piv = a[right]; lo = left; hi = right;
		while (lo <= hi) {
			if (a[hi] > piv) {
				hi--;
			} else {
				swap a[lo],a[hi];
				lo++;
			}
		}
		quicksort(left,hi);
		quicksort(lo,right);
	}	

	Ref: Schwoon, Stefan. Model-checking pushdown systems. Diss. Technische Universität München, 2002. 
	
*/

program:
bool sorted;
u6[2] a;

main() {
	a[0u2] = *;
	a[1u2] = *;
	qs(0u2, 1u2);
}

qs(u2 left, u2 right) {
	u2 lo, hi;
	u6 piv;

	if (left >= right) {
	} else {
		piv = a[right]; 
		lo = left;
		hi = right;
		while (lo <= hi) { 
			if (a[hi] > piv){
				hi = hi - 1u2; 
			} else {
				swapElements(lo, hi);
				lo = lo + 1u2;
			}
		}
		qs(left, hi);
		qs(lo, right);
	}
}

swapElements(u2 swapLeft, u2 swapRight) {
    u6 tmp;
    
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
	sorted = a[0u2] <= a[1u2];
}

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
u10[2] a;

main() {
	a[0s3] = *;
	a[1s3] = *;
	qs(0s3, 1s3);
}

qs(s3 left, s3 right) {
	s3 lo, hi;
	u10 piv;

	if (left >= right) {
	} else {
		piv = a[right]; 
		lo = left;
		hi = right;
		while (lo <= hi) { 
			if (a[hi] > piv){
				hi = hi - 1s3; 
			} else {
				swapElements(lo, hi);
				lo = lo + 1s3;
			}
		}
		qs(left, hi);
		qs(lo, right);
	}
}

swapElements(s3 swapLeft, s3 swapRight) {
    u10 tmp;
    
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
	sorted = a[0s3] <= a[1s3];
}

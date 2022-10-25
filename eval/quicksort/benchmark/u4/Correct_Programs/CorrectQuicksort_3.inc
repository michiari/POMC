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
u4[3] a;

main() {
	a[0s3] = *;
	a[1s3] = *;
	a[2s3] = *;
	qs(0s3, 2s3);
}

qs(s3 left, s3 right) {
	s3 lo, hi, eq;
	u4 piv;

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
    u4 tmp;
    
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
	sorted = a[0s3] <= a[1s3] && a[1s3] <= a[2s3];
}

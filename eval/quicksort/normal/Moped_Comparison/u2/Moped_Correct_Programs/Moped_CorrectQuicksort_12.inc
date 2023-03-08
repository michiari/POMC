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
bool ok;
u2[12] a;

main() {
	a[0s5] = *;
	a[1s5] = *;
	a[2s5] = *;
	a[3s5] = *;
	a[4s5] = *;
	a[5s5] = *;
	a[6s5] = *;
	a[7s5] = *;
	a[8s5] = *;
	a[9s5] = *;
	a[10s5] = *;
	a[11s5] = *;
	qs(0s5, 11s5);
	ok = a[0s5] <= a[1s5] && a[1s5] <= a[2s5] && a[2s5] <= a[3s5] && a[3s5] <= a[4s5] && a[4s5] <= a[5s5] && a[5s5] <= a[6s5] && a[6s5] <= a[7s5] && a[7s5] <= a[8s5] && a[8s5] <= a[9s5] && a[9s5] <= a[10s5] && a[10s5] <= a[11s5]; 
}

qs(s5 left, s5 right) {
	s5 lo, hi, eq;
	u2 piv;

	if (left >= right) {
	} else {
		piv = a[right]; 
		eq = left;
		lo = eq;
		hi = right;
		while (lo <= hi) { 
			if (a[hi] > piv){
				hi = hi - 1s5; 
			} else {
				swapElements(lo, hi);
				if (a[lo] < piv){
					swapElements(lo, eq);
					eq = eq + 1s5;
				} else {}
				lo = lo + 1s5;
			}
		}
		qs(left,eq-1s5);
		qs(lo,right);
	}
}

swapElements(s5 swapLeft, s5 swapRight) {
    u2 tmp;
    
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
}

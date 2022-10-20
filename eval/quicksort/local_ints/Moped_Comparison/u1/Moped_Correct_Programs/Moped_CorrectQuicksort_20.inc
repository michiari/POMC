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
u1[20] a;

main() {
	a[0s6] = *;
	a[1s6] = *;
	a[2s6] = *;
	a[3s6] = *;
	a[4s6] = *;
	a[5s6] = *;
	a[6s6] = *;
	a[7s6] = *;
	a[8s6] = *;
	a[9s6] = *;
	a[10s6] = *;
	a[11s6] = *;
	a[12s6] = *;
	a[13s6] = *;
	a[14s6] = *;
	a[15s6] = *;
	a[16s6] = *;
	a[17s6] = *;
	a[18s6] = *;
	a[19s6] = *;
	qs(0s6, 19s6);
	ok = a[0s6] <= a[1s6] && a[1s6] <= a[2s6] && a[2s6] <= a[3s6] && a[3s6] <= a[4s6] && a[4s6] <= a[5s6] && a[5s6] <= a[6s6] && a[6s6] <= a[7s6] && a[7s6] <= a[8s6] && a[8s6] <= a[9s6] && a[9s6] <= a[10s6] && a[10s6] <= a[11s6] && a[11s6] <= a[12s6] && a[12s6] <= a[13s6] && a[13s6] <= a[14s6] && a[14s6] <= a[15s6] && a[15s6] <= a[16s6] && a[16s6] <= a[17s6] && a[17s6] <= a[18s6] && a[18s6] <= a[19s6]; 
}

qs(s6 left, s6 right) {
	s6 lo, hi, eq;
	u1 piv;

	if (left >= right) {
	} else {
		piv = a[right]; 
		eq = left;
		lo = eq;
		hi = right;
		while (lo <= hi) { 
			if (a[hi] > piv){
				hi = hi - 1s6; 
			} else {
				swapElements(lo, hi);
				if (a[lo] < piv){
					swapElements(lo, eq);
					eq = eq + 1s6;
				} else {}
				lo = lo + 1s6;
			}
		}
		qs(left,eq-1s6);
		qs(lo,right);
	}
}

swapElements(s6 swapLeft, s6 swapRight) {
    u1 tmp;
    
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
}

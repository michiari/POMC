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
u1[40] a;

main() {
	a[0s7] = *;
	a[1s7] = *;
	a[2s7] = *;
	a[3s7] = *;
	a[4s7] = *;
	a[5s7] = *;
	a[6s7] = *;
	a[7s7] = *;
	a[8s7] = *;
	a[9s7] = *;
	a[10s7] = *;
	a[11s7] = *;
	a[12s7] = *;
	a[13s7] = *;
	a[14s7] = *;
	a[15s7] = *;
	a[16s7] = *;
	a[17s7] = *;
	a[18s7] = *;
	a[19s7] = *;
	a[20s7] = *;
	a[21s7] = *;
	a[22s7] = *;
	a[23s7] = *;
	a[24s7] = *;
	a[25s7] = *;
	a[26s7] = *;
	a[27s7] = *;
	a[28s7] = *;
	a[29s7] = *;
	a[30s7] = *;
	a[31s7] = *;
	a[32s7] = *;
	a[33s7] = *;
	a[34s7] = *;
	a[35s7] = *;
	a[36s7] = *;
	a[37s7] = *;
	a[38s7] = *;
	a[39s7] = *;

	qs(0s7, 39s7);
	ok = a[0s7] <= a[1s7] && a[1s7] <= a[2s7] && a[2s7] <= a[3s7] && a[3s7] <= a[4s7] && a[4s7] <= a[5s7] && a[5s7] <= a[6s7] && a[6s7] <= a[7s7] && a[7s7] <= a[8s7] && a[8s7] <= a[9s7] && a[9s7] <= a[10s7] && a[10s7] <= a[11s7] && a[11s7] <= a[12s7] && a[12s7] <= a[13s7] && a[13s7] <= a[14s7] && a[14s7] <= a[15s7] && a[15s7] <= a[16s7] && a[16s7] <= a[17s7] && a[17s7] <= a[18s7] && a[18s7] <= a[19s7] && a[19s7] <= a[20s7] && a[20s7] <= a[21s7] && a[21s7] <= a[22s7] && a[22s7] <= a[23s7] && a[23s7] <= a[24s7] && a[24s7] <= a[25s7] && a[25s7] <= a[26s7] && a[26s7] <= a[27s7] && a[27s7] <= a[28s7] && a[28s7] <= a[29s7] && a[29s7] <= a[30s7] && a[30s7] <= a[31s7] && a[31s7] <= a[32s7] && a[32s7] <= a[33s7] && a[33s7] <= a[34s7] && a[34s7] <= a[35s7] && a[35s7] <= a[36s7] && a[36s7] <= a[37s7] && a[37s7] <= a[38s7] && a[38s7] <= a[39s7];
}

qs(s7 left, s7 right) {
	s7 lo, hi, eq;
	u1 piv;

	if (left >= right) {
	} else {
		piv = a[right]; 
		eq = left;
		lo = eq;
		hi = right;
		while (lo <= hi) { 
			if (a[hi] > piv){
				hi = hi - 1s7; 
			} else {
				swapElements(lo, hi);
				if (a[lo] < piv){
					swapElements(lo, eq);
					eq = eq + 1s7;
				} else {}
				lo = lo + 1s7;
			}
		}
		qs(left,eq-1s7);
		qs(lo,right);
	}
}

swapElements(s7 swapLeft, s7 swapRight) {
    u1 tmp;
    
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
}

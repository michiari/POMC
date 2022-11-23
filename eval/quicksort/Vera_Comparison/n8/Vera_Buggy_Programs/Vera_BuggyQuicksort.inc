/*  Corresponding (abstracted) procedure in C syntax:

	void quicksort (int left,int right)
	{
		int lo,hi;
		if (left >= right) return;
		lo = left; hi = right;
		while (lo <= hi) {
			if (hi == right || ∗) {
				lo++;
			} else {
				hi--;
			}
		}
		quicksort(left,hi);
		quicksort(lo,right);
	}

	Ref: Schwoon, Stefan. Model-checking pushdown systems. Diss. Technische Universität München, 2002. 
	
*/

program:

main() {
	u8 left, right;
	left  = *;
	right = *;
	qs(left, right);
}

qs(u8 left, u8 right) {
	u8 lo, hi;
	bool nondet;

	if (left >= right) {
	} else {
		lo = left;
		hi = right;
		while (lo <= hi) { 
			if (*) {
				nondet = true;
			} else {
				nondet = false;
			}
			if (hi == right || nondet) {
				lo = lo + 1u8; 
			} else {
				hi = hi - 1u8;
			}
		}
		qs(left, hi);
		qs(lo, right);
	}
}

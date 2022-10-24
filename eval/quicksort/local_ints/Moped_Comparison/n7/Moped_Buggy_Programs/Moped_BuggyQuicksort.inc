/*  Corresponding procedure in C syntax:

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
	u7 left, right;
	left  = *;
	right = *;
	qs(left, right);
}

qs(u7 left, u7 right) {
	u7 lo, hi;
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
				lo = lo + 1u7; 
			} else {
				hi = hi - 1u7;
			}
		}
		qs(left, hi);
		qs(lo, right);
	}
}

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
 	u3 left, right;
	left  = *;
	right = *;
	qs(left, right);
}

qs(u3 left, u3 right) {
	u3 lo, hi;
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
				lo = lo + 1u3; 
			} else {
				hi = hi - 1u3;
			}
		}
		qs(left, hi);
		qs(lo, right);
	}
}

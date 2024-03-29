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
bool  sorted;
s3 left, right, lo, hi, swapLeft, swapRight;
u8 piv, tmp;
u8[2] a;

main() {
	left = 0s3;
	right = 1s3;
	a[0s3] = *;
	a[1s3] = *;
	qs();
}

qs() {
	if (left >= right) {
	} else {
		piv = a[right]; 
		lo = left;
		hi = right;
		while (lo <= hi) { 
			if (a[hi] > piv){
				hi = hi - 1s3; 
			} else {
				swapLeft = lo;
				swapRight = hi;
				swapElements();
				lo = lo + 1s3;
			}
		}

		// recursive calls
		if (lo == 0s3 && right == 1s3){
			qsRec0();
		} else {
			qsRec1();
		}
	}
}

swapElements() {
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
	sorted = a[0s3] <= a[1s3];
}

//recursive cases depending on the value of lo and right for a two-elements array
qsRec0() {
	right = hi;
	qs();
	left = 0s3; 
	right = 1s3;
	qs();
}

qsRec1() {
	right = hi;
	qs();
	//abort second recursive call, it involves at most one element
	//qs();
}


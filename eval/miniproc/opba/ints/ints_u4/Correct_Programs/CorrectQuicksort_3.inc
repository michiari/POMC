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
		quicksort(left,eq-1s3);
		quicksort(lo,right);
	}

	Ref: Schwoon, Stefan. Model-checking pushdown systems. Diss. Technische Universität München, 2002. 
*/

program:
bool  okay;
s3 left, right, lo, hi, eq;
u4 piv, swapLeft, swapRight, tmp;
u4[3] a;


main() {
	left = 0s3;
	right = 2s3;
	a[0s3] = *;
	a[1s3] = *;
	a[2s3] = *;
	qs();
}

qs() {
	if (left >= right) {
	} else {
		piv = a[right]; 
		eq = left;
		lo = eq;
		hi = right;
		while (lo <= hi) { 
			qsif();
		}

		// recursive calls
		if (lo == 0s3 && right == 1s3){
			qsRec0();
		} else {
			if (lo == 0s3 && right == 2s3){
				qsRec1();
			} else {
				if (lo == 1s3 && right == 2s3){
					qsRec2();
				} else {
					qsRec3();
				}
			} 
		}
	}
}

qsif() { 
	if (a[hi] > piv){
		hi = hi - 1s3; 
	} else {
		swapLeft = lo;
		swapRight = hi;
		swapElements();
		if (a[lo] < piv){
			swapLeft = lo;
			swapRight = eq;
			swapElements();
		} else {}
		lo = lo + 1s3;
	}
}

swapElements() {
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
	okay = a[0s3] <= a[1s3] && a[1s3] <= a[2s3];
}

//recursive cases depending on the value of lo and right for a three-elements array
qsRec0() {
	right = eq - 1s3;
	qs();
	left = 0s3; 
	right = 1s3;
	qs();
}

qsRec1() {
	right = eq - 1s3;
	qs();
	left = 0s3; 
	right = 2s3;
	qs();
}

qsRec2() {
	right = eq - 1s3;
	qs();
	left = 1s3; 
	right = 2s3;
	qs();
}

qsRec3() {
	right = eq - 1s3;
	qs();
	//abort second recursive call, it involves at most one element
	//qs();
}
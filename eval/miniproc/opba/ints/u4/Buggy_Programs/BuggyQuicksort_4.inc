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
s4 left, right, lo, hi, swapLeft, swapRight;
u4 piv, tmp;
u4[4] a;

main() {
	left = 0s4;
	right = 3s4;
	a[0s4] = *;
	a[1s4] = *;
	a[2s4] = *;
	a[3s4] = *;
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
				hi = hi - 1s4; 
			} else {
				swapLeft = lo;
				swapRight = hi;
				swapElements();
				lo = lo + 1s4;
			}
		}

		// recursive calls
		if (lo == 0s4 && right == 1s4){
			qsRec0();
		} else {
			if (lo == 0s4 && right == 2s4){
				qsRec1();
			} else {
				if (lo == 0s4 && right == 3s4){
					qsRec2();
				} else {
					if (lo == 1s4 && right == 2s4){
						qsRec3();
					} else {
						if (lo == 1s4 && right == 3s4){
							qsRec4();
						} else {
							if (lo == 2s4 && right == 3s4){
								qsRec5();
							} else {
								qsRec6();
							}
						}
					}
				}
			} 
		}
	}
}

swapElements() {
	tmp = a[swapLeft];
	a[swapLeft] = a[swapRight];
	a[swapRight] = tmp;
	sorted = a[0s4] <= a[1s4] && a[1s4] <= a[2s4] && a[2s4] <= a[3s4];
}

//recursive cases depending on the value of lo and right for a four-elements array
qsRec0() {
	right = hi;
	qs();
	left = 0s4; 
	right = 1s4;
	qs();
}

qsRec1() {
	right = hi;
	qs();
	left = 0s4; 
	right = 2s4;
	qs();
}

qsRec2() {
	right = hi;
	qs();
	left = 0s4; 
	right = 3s4;
	qs();
}

qsRec3() {
	right = hi;
	qs();
	left = 1s4; 
	right = 2s4;
	qs();
}

qsRec4() {
	right = hi;
	qs();
	left = 1s4; 
	right = 3s4;
	qs();
}

qsRec5() {
	right = hi;
	qs();
	left = 2s4; 
	right = 3s4;
	qs();
}

qsRec6() {
	right = hi;
	qs();
	//abort second recursive call, it involves at most one element
	//qs();
}
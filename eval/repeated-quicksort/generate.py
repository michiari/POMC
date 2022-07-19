#!/usr/bin/env python3
import fileinput

formulas = ["F (ret And main)",              #01
            "XNu (ret And main)",            #02
            "~ (F (ret And main))",          #03
            "~ (XNu (ret And main))",        #04
            "G ( exc Implies (XBu han))"     #05
            ] 

for u_size in range(1,5):
    for arr_size in range(2,8):
        filein = 'Programs/' + 'Quicksort_' + str(arr_size) + '.inc';
        fileout = 'u' + str(u_size) + '/' +'Programs/' +'Quicksort_' + str(arr_size) + '.inc';
        f1 = open(filein, 'r')
        f2 = open(fileout, 'w')
        for line in f1:
            f2.write(line.replace('u*', 'u' + str(u_size)))
        f1.close()
        f2.close()
        n = 1;
        m = 0;
        for form in formulas:
            with open('u' + str(u_size) +  '/' + "repeated" + '-' + str(u_size) + '.' + str(arr_size) + '.' + str(m) + str(n) +'.pomc', 'w') as f:
                f.write('formulas = ' + form + ';\n')
                f.write('include = "' + 'Programs/'  +'Quicksort_' + str(arr_size) + '.inc";')
            n += 1
            if n==10:
                m +=1;
                n = 0;

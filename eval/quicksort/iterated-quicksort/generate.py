#!/usr/bin/env python3
import fileinput

formulas = ["~ (XNu ((ret And main) Or (exc)))",   #01  RQ1 - True
            "G ( exc Implies (XBu han))",     #02   RQ2 - True
            "G (F (call And qs))",    #03           RQ3 - True
            "G ((call And qs And (PBd han)) --> ( (XNu (ret And qs And sorted)) Or (XNu (exc And maxReached)))) " #04
            ] 

for u_size in range(1,5):
    for arr_size in range(2,8):
        filein = 'Repeated_Programs/' + 'RepeatedQuicksort_' + str(arr_size) + '.inc';
        fileout = 'benchmark/u' + str(u_size) + '/' +'Repeated_Programs/' +'RepeatedQuicksort_' + str(arr_size) + '.inc';
        f1 = open(filein, 'r')
        f2 = open(fileout, 'w')
        for line in f1:
            f2.write(line.replace('u*', 'u' + str(u_size)))
        f1.close()
        f2.close()
        n = 1;
        m = 0;
        for form in formulas:
            with open('benchmark/u' + str(u_size) +  '/Repeated/' + "repeated" + '-' + str(u_size) + '.' + str(arr_size) + '.' + str(m) + str(n) +'.pomc', 'w') as f:
                f.write('formulas = ' + form + ';\n')
                f.write('include = "' + '../Repeated_Programs/'  +'RepeatedQuicksort_' + str(arr_size) + '.inc";')
            n += 1
            if n==10:
                m +=1;
                n = 0;

#!/usr/bin/env python3
import fileinput

Buggy_formulas =  [   "F (ret And main)",        #01
                "XNu (ret And main)",            #02
                "F ( G (sorted))",                 #03
                "XNu (sorted)",                    #04
                "F (ret And main And (sorted))",   #05
                "XNu (ret And main And (sorted))"] #06

Correct_formulas = [    "F (ret And main)",      #01
                "XNu (ret And main)",            #02
                "F ( G (sorted))",                 #03
                "XNu (sorted)",                    #04
                "F (ret And main And (sorted))",   #05
                "XNu (ret And main And (sorted))"] #06

SemiSafe_formulas = [   "F (ret And main)",                                                                         #01
                        "XNu (ret And main)",                                                                       #02
                        "F ( G (sorted))",                                                                            #03
                        "XNu (sorted)",                                                                               #04
                        "G ((call And main) --> ~ (PNu exc Or XNu exc))",                                           #05
                        "G ((call And qs) --> ~ (PNu exc Or XNu exc))",                                             #06
                        "((PNu exc) Or (XNu exc)) --> ((PNu (exc And hasParsed)) Or (XNu (exc And hasParsed)))",    #07
                        "((PNu exc) Or (XNu exc)) --> ((PNu (exc And sorted)) Or (XNu (exc And sorted)))",              #08
                        "G ( (call And accessValues) --> (hasParsed) Or (T Sd han ))",                              #09
                        "(F (ret And main)) Or (XNu (exc And hasParsed))",                                          #10
                        "(XNu (ret And main)) Or (XNu (exc And hasParsed))",                                        #11
                        "(F ( G (sorted))) Or (XNu (exc And hasParsed))",                                             #12
                        "(XNu (sorted)) Or (XNu (exc And hasParsed))",                                                #13
                        "(F (ret And main And (sorted))) Or (XNu (exc And hasParsed))"]                               #14



Experiments = [(Buggy_formulas,"Buggy") , (Correct_formulas,"Correct"), (SemiSafe_formulas,"SemiSafe")]

for u_size in range(1,5):
    for (exp,name) in Experiments:
        for arr_size in range(2,8):
            filein = name + '_Programs/' + name +'Quicksort_' + str(arr_size) + '.inc';
            fileout = 'u' + str(u_size) + '/' + name + '_Programs/' + name +'Quicksort_' + str(arr_size) + '.inc';
            f1 = open(filein, 'r')
            f2 = open(fileout, 'w')
            for line in f1:
                f2.write(line.replace('u*', 'u' + str(u_size)))
            f1.close()
            f2.close()
            n = 1;
            m = 0;
            for form in exp:
                with open('u' + str(u_size) + '/' + name + '/' + name. lower() + '-' + str(u_size) + '.' + str(arr_size) + '.' + str(m) + str(n) +'.pomc', 'w') as f:
                    f.write('formulas = ' + form + ';\n')
                    f.write('include = "../' + name + '_Programs/' + name +'Quicksort_' + str(arr_size) + '.inc";')
                n += 1
                if n==10:
                    m +=1;
                    n = 0;

# generate experiments for comparing POMC with Vera
for u_size in [4,6,8,10,32]:
    filein = 'Buggy_Programs/BuggyQuicksort_2.inc';
    fileout = 'Vera_Comparison/u' + str(u_size) + '/Buggy_Programs/BuggyQuicksort_2' + '.inc'
    f1 = open(filein, 'r')
    f2 = open(fileout, 'w')
    for line in f1:
        f2.write(line.replace('u*', 'u' + str(u_size)))
    f1.close()
    f2.close()
    n = 1;
    m = 0;
    for form in Buggy_formulas:
                with open( 'Vera_Comparison/u' + str(u_size) + '/Buggy/buggy-' + str(u_size) + '.2.' + str(m) + str(n) +'.pomc', 'w') as f:
                    f.write('formulas = ' + form + ';\n')
                    f.write('include = "../Buggy_Programs/BuggyQuicksort_2.inc";')
                n += 1
                if n==10:
                    m +=1;
                    n = 0;
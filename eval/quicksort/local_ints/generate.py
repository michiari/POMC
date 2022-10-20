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
                        "XNu (ret And main)",                                                                       #02   Q1 - False
                        "F ( G (sorted))",                                                                          #03
                        "XNu (sorted)",                                                                             #04   Q2 - False
                        "G ((call And main) --> ~ (PNu exc Or XNu exc))",                                           #05   Q3 - False
                        "G ((call And qs) --> ~ (PNu exc Or XNu exc))",                                             #06   Q4 - False
                        "((PNu exc) Or (XNu exc)) --> ((PNu (exc And hasParsed)) Or (XNu (exc And hasParsed)))",    #07   Q5 - True
                        "((PNu exc) Or (XNu exc)) --> ((PNu (exc And sorted)) Or (XNu (exc And sorted)))",          #08   Q6 - False
                        "G ( (call And accessValues) --> (hasParsed) Or (T Sd han ))",                              #09   Q7 - True
                        "(F (ret And main)) Or (XNu (exc And hasParsed))",                                          #10
                        "(XNu (ret And main)) Or (XNu (exc And hasParsed))",                                        #11   Q8 - True
                        "(F ( G (sorted))) Or (XNu (exc And hasParsed))",                                           #12   
                        "(XNu (sorted)) Or (XNu (exc And hasParsed))",                                              #13   Q9 - True
                        "(F (ret And main And (sorted))) Or (XNu (exc And hasParsed))"]                             #14   Q10 - True 


Experiments = [(Buggy_formulas,"Buggy") , (Correct_formulas,"Correct"), (SemiSafe_formulas,"SemiSafe")]

for u_size in range(1,5):
    for (exp,name) in Experiments:
        for arr_size in range(2,8):
            filein = name + '_Programs/' + name +'Quicksort_' + str(arr_size) + '.inc';
            fileout = 'benchmark/u' + str(u_size) + '/' + name + '_Programs/' + name +'Quicksort_' + str(arr_size) + '.inc';
            f1 = open(filein, 'r')
            f2 = open(fileout, 'w')
            for line in f1:
                f2.write(line.replace('u*', 'u' + str(u_size)))
            f1.close()
            f2.close()
            for index,form in enumerate(exp, start=1):
                with open('benchmark/u' + str(u_size) + '/' + name + '/' + name. lower() + '-' + str(u_size) + '.' + str(arr_size) + '.' + str(index).zfill(2) +'.pomc', 'w') as f:
                    f.write('formulas = ' + form + ';\n')
                    f.write('include = "../' + name + '_Programs/' + name +'Quicksort_' + str(u_size) + '.' + str(arr_size) + '.inc";')

# generate experiments for comparing POMC with Vera
for u_size in [4,6,8,10,32]:
    filein = 'Buggy_Programs/BuggyQuicksort_2.inc';
    fileout = 'Vera_Comparison/u' + str(u_size) + '/BuggyQuicksort_2.inc'
    f1 = open(filein, 'r')
    f2 = open(fileout, 'w')
    for line in f1:
        f2.write(line.replace('u*', 'u' + str(u_size)))
    f1.close()
    f2.close()
    with open( 'Vera_Comparison/u' + str(u_size) + '/buggy-' + str(u_size) + '.2.01.pomc', 'w') as f:
        f.write('formulas = ' + Buggy_formulas[0] + ';\n')
        f.write('include = "/BuggyQuicksort_2.inc";')

# experiments for comparison POMC with MOPED have been hadnwritten

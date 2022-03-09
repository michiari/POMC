#!/usr/bin/env python3
import fileinput

Buggy_formulas =  [   "F (ret And main)",
                "XNu (ret And main)",
                #"(F (G (~ dup))) <--> (F (ret And main))",
                "F ( G (okay))",
                "XNu (okay)",
                "F (ret And main And (okay))",
                "XNu (ret And main And (okay))"]

Correct_formulas = [    "F (ret And main)",
                "XNu (ret And main)",
                "F ( G (okay))",
                "XNu (okay)",
                "F (ret And main And (okay))",
                "XNu (ret And main And (okay))" ]

SemiSafe_formulas = [   "F (ret And main)",
                        "XNu (ret And main)", 
                        "F ( G (okay))",
                        "XNu (okay)", 
                        "G ((call And main) --> ~ (PNu exc Or XNu exc))", 
                        "G ((call And qs) --> ~ (PNu exc Or XNu exc))", 
                        "((PNu exc) Or (XNu exc)) --> ((PNu (exc And hasParsed)) Or (XNu (exc And hasParsed)))", 
                        "((PNu exc) Or (XNu exc)) --> ((PNu (exc And okay)) Or (XNu (exc And okay)))", 
                        "G ( (call And accessValues) --> (hasParsed) Or (T Sd han ))", 
                        "(F (ret And main)) Or (XNu (exc And hasParsed))", 
                        "(XNu (ret And main)) Or (XNu (exc And hasParsed))", 
                        "(F ( G (okay))) Or (XNu (exc And hasParsed))", 
                        "(XNu (okay)) Or (XNu (exc And hasParsed))", 
                        "(F (ret And main And (okay))) Or (XNu (exc And hasParsed))"]



Experiments = [(Buggy_formulas,"Buggy") , (Correct_formulas,"Correct"), (SemiSafe_formulas,"SemiSafe")]

for u_size in range(1,5):
    for (exp,name) in Experiments:
        for arr_size in range(2,8):
            n = 1;
            m = 0;
            for form in exp:
                filein = name + '_Programs/' + name +'Quicksort_' + str(arr_size) + '.inc';
                fileout = 'ints_u' + str(u_size) + '/' + name + '_Programs/' + name +'Quicksort_' + str(arr_size) + '.inc';
                f1 = open(filein, 'r')
                f2 = open(fileout, 'w')
                for line in f1:
                    f2.write(line.replace('u*', 'u' + str(u_size)))
                f1.close()
                f2.close()
                with open('ints_u' + str(u_size) + '/' + name + '/' + name. lower() + '-' + str(u_size) + '.' + str(arr_size) + '.' + str(m) + str(n) +'.pomc', 'w') as f:
                    f.write('formulas = ' + form + ';\n')
                    f.write('include = "../' + name + '_Programs/' + name +'Quicksort_' + str(arr_size) + '.inc";')
                n += 1
                if n==10:
                    m +=1;
                    n = 0;

                
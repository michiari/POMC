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

SemiSafe_formulas = [   "formulas = F (ret And main)",
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

for (exp,name) in Experiments:
    for size in range(2,8):
        n = 1
        for form in exp:
            with open(name + '/' + name. lower() + '-' + str(size) + '.' + str(n) +'.pomc', 'w') as f:
                f.write('formulas = ' + form + ';\n')
                f.write('include = "../' + name + '_Programs/' + name +'Quicksort_' + str(size) + '.inc";')
            n += 1
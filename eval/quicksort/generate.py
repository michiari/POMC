#!/usr/bin/env python3
import fileinput

Buggy_formulas =  [   "F (ret And main)",        #01
                "XNu (ret And main)",            #02  BQ.2 - False
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
                        "XNu (ret And main)",                                                                       #02   Q.1 - False
                        "F ( G (sorted))",                                                                          #03
                        "XNu (sorted)",                                                                             #04   Q.2 - False
                        "G ((call And main) --> ~ (PNu exc Or XNu exc))",                                           #05   Q.3 - False
                        "G ((call And qs) --> ~ (PNu exc Or XNu exc))",                                             #06   Q.4 - False
                        "((PNu exc) Or (XNu exc)) --> ((PNu (exc And hasParsed)) Or (XNu (exc And hasParsed)))",    #07   Q.5 - True
                        "((PNu exc) Or (XNu exc)) --> ((PNu (exc And sorted)) Or (XNu (exc And sorted)))",          #08   Q.6 - False
                        "G ( (call And accessValues) --> (hasParsed) Or (T Sd han ))",                              #09   Q.7 - True
                        "(F (ret And main)) Or (XNu (exc And hasParsed))",                                          #10
                        "(XNu (ret And main)) Or (XNu (exc And hasParsed))",                                        #11   Q.8 - True
                        "(F ( G (sorted))) Or (XNu (exc And hasParsed))",                                           #12   
                        "(XNu (sorted)) Or (XNu (exc And hasParsed))",                                              #13   Q.9 - True
                        "(F (ret And main And (sorted))) Or (XNu (exc And hasParsed))"]                             #14   Q.10 - True 


Benchmark = [(Buggy_formulas,"Buggy") , (Correct_formulas,"Correct"), (SemiSafe_formulas,"SemiSafe")]

for u_size in range(1,5):
    for (exp,name) in Benchmark:
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
                    f.write('include = "../' + name + '_Programs/' + name +'Quicksort_' + str(arr_size) + '.inc";')

# experiments for comparing POMC with VERA have been handwritten
# the VERA formula we verify is:
#   1) F (ret And main)  ----- BQ.1 - False

# experiments for comparing POMC with MOPED have been handwritten
# the MOPED formulae we verify are 
#   1) F (ret And main) for the buggy version, and   
#   2) F (ok) for the correct version, which both verifies correctness and termination.

# MODELS:
# the model for VERA and MOPED-buggy are the same, modulo the parameter N
# it represents an ABSTRACT version of the Buggy model from the benchmark

# the model for MOPED-correct and Correct (from the benchmark) are the same, modulo the parameters (K,M) AND
# a different way to establish if the array is sorted (MOPED uses variable "ok" and sets it just once at the end,
# Correct uses variable "sorted" and updates it at every swap.)
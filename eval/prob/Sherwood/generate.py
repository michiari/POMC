#!/usr/bin/env python3
import fileinput
import math
import os

term_benchmark = [('', "term")]

qual_benchmark = [
    ("G ((call And B And sorted And valOccurs And [B|left <= right]) --> XNu correctIndex);\n// S1: Partial Correctness", "S1"), # partial correctness
    ("G ((call And B And sorted And (~ valOccurs) And [B|left <= right]) --> XNu ( ~ correctIndex));\n// S2: Dual Partial Correctness", "S2"), # dual partial correctness
    ("G ((call And B And sorted And valOccurs And [B|left < right]) --> PNd (F (call And B)));\n// S5: Stack inspection (LTL)", "S3"), # stack inspection (LTL)
    ("G ((call And B And sorted And (~ valOccurs) And [B|left < right]) --> PNd (F (call And B)));\n// S6: Stack inspection (v2) (LTL)", "S4") # stack inspection (v2) (LTL)
    
    #("G ((call And B And sorted And valOccurs And [B|left < right]) --> XNd (call And B));\n// S3: Stack inspection", "S5"), # stack inspection
    #("G ((call And B And sorted And (~ valOccurs) And [B|left < right]) --> XNd (call And B));\n// S4: Stack inspection (v2)", "S6"), # stack inspection (v2)
    ]

quant_benchmark = [
    #("G ((call And B And sorted And valOccurs And [B|left <= right]) --> XNu correctIndex);\n// S1: Partial Correctness", "S1"), # partial correctness
    #("G ((call And B And sorted And (~ valOccurs) And [B|left <= right]) --> XNu ( ~ correctIndex));\n// S2: Dual Partial Correctness", "S2"), # dual partial correctness
    ("G ((call And B And sorted And valOccurs And [B|left < right]) --> PNd (F (call And B)));\n// S5: Stack inspection (LTL)", "S3"), # stack inspection (LTL)
    #("G ((call And B And sorted And (~ valOccurs) And [B|left < right]) --> PNd (F (call And B)));\n// S6: Stack inspection (v2) (LTL)", "S4") # stack inspection (v2) (LTL)
    
    #("G ((call And B And sorted And valOccurs And [B|left < right]) --> XNd (call And B));\n// S3: Stack inspection", "S5"), # stack inspection
    #("G ((call And B And sorted And (~ valOccurs) And [B|left < right]) --> XNd (call And B));\n// S4: Stack inspection (v2)", "S6"), # stack inspection (v2)
    ]

queries = [ ('qualitative',[(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7), (2,1), (2,2), (2,3), (2,4), (3,1), (3,2), (4,1), (4,2)], qual_benchmark)
          , ('approximate',[(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7), (2,1), (2,2), (2,3), (2,4), (3,1), (3,2), (4,1), (4,2)], term_benchmark)
          , ('quantitative',[(1,1), (1,2), (1,3), (2,1), (2,2), (3,1), (4,1)],quant_benchmark)]

def array_domain_comment(bits):
    return '// Elements domain bits: K = ' + str(bits) + ';'

def array_domain_assignment(bits):
    return 'max_array_value = ' + str(int(math.pow(2,bits) - 1)) + 'u4;'

def array_length_comment(len):
    return '// Array length: M = ' + str(len) + ';'

def array_length_assignment(len):
    return 'max_array_index = ' + str(len -1) + 'u4;'

def build_query(query, exp):
    if exp:
        return 'probabilistic query: ' + query + ';\nformula = ' + exp
    else: return 'probabilistic query: ' + query + ';\n'

# model file
filein = 'Sherwood.txt'

# remove benchmark folder if already present
if os.path.isfile('benchmark/'):
    os.remove('benchmark/')

for (query, valuations, bench) in queries:
    for (exp, name) in bench:
        prob_query = build_query(query, exp)
        for (u_size, arr_size) in valuations:
            arr_domain_comm = array_domain_comment(u_size)
            arr_domain_ass = array_domain_assignment(u_size)
            arr_len_comm = array_length_comment(arr_size)
            arr_len_ass = array_length_assignment(arr_size)
            fileout = 'benchmark/' + query + '/' + name + '/sherwood-' + str(u_size) + '.' + str(arr_size) + '.' + name + '.pomc'
            with open(filein, 'r') as f1:
                os.makedirs(os.path.dirname(fileout), exist_ok=True)
                with open(fileout, 'w+') as f2:
                    for line in f1:
                        f2.write(
                            line.replace('probabilistic query;', prob_query) # adding the formula
                                .replace('// Elements\' domain bits: K = *;', arr_domain_comm) # fixing the domain of array values
                                .replace('max_array_value = *;', arr_domain_ass)
                                .replace('// Array length: M = *;', arr_len_comm) # fixing array length
                                .replace('max_array_index = *;', arr_len_ass)
                            )
                            
# Checking Sherwood properties with Storm
# Q19: storm --explicit sherwood-1.2.Q20.tra sherwood-1.2.Q20.lab --prop "P=? [G ((\"call\" & \"b\" & \"sorted\" & \"valoccurs\" & \"bleftright\") => X (F (\"call\" & \"b\")))]"
# Q20: storm --explicit sherwood-1.7.Q20.tra sherwood-1.2.Q20.lab --prop "P=? [G ( (! (\"call\" & \"b\" & \"sorted\" & (! \"valoccurs\") & \"bleftright\")) | (X (F (\"call\" & \"b\"))))]"


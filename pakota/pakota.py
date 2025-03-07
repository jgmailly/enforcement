#!/usr/bin/env python3

## Copyright (c) <2025> <Andreas Niskanen, University of Helsinki>
## 
## 
## 
## Permission is hereby granted, free of charge, to any person obtaining a copy
## of this software and associated documentation files (the "Software"), to deal
## in the Software without restriction, including without limitation the rights
## to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
## copies of the Software, and to permit persons to whom the Software is
## furnished to do so, subject to the following conditions:
## 
## 
## 
## The above copyright notice and this permission notice shall be included in
## all copies or substantial portions of the Software.
## 
## 
## 
## THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
## IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
## FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT.  IN NO EVENT SHALL THE
## AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
## LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
## OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
## THE SOFTWARE.

from pysat.examples.rc2 import RC2, RC2Stratified
from pysat.formula import WCNF
from pysat.solvers import Glucose3
from pysat.card import *
CARD_ENCODING = EncType.sortnetwrk

import argparse, os, sys, itertools, resource

def get_utime():
    self_utime = resource.getrusage(resource.RUSAGE_SELF).ru_utime
    children_utime = resource.getrusage(resource.RUSAGE_CHILDREN).ru_utime
    return self_utime + children_utime

class AF():

    def __init__(self, args, atts, semantics='', pos_cred_enfs=[], neg_cred_enfs=[], pos_skept_enfs=[], neg_skept_enfs=[],
        pos_conjunct_enfs=[], neg_conjunct_enfs=[], pos_cred_weight=float("inf"), neg_cred_weight=float("inf"),
        pos_skept_weight=float("inf"), neg_skept_weight=float("inf"), pos_conjunct_weight=float("inf"), neg_conjunct_weight=float("inf"),
        pos_attacks=[], neg_attacks=[], static=False):
        self.args = list(range(len(args)))
        self.int_to_arg = args
        self.arg_to_int = { self.int_to_arg[arg] : arg for arg in self.args }
        self.atts = [(self.arg_to_int[s], self.arg_to_int[t]) for s,t in atts]
        self.var_counter = itertools.count(1)
        self.att_exists = { (a,b) : False for a in self.args for b in self.args }
        for a,b in self.atts:
            self.att_exists[(a,b)] = True

        if static:
            self.attackers = { a : [] for a in self.args }
            for a,b in self.atts:
                self.attackers[b].append(a)
            self.arg_accepted_var = { a : next(self.var_counter) for a in self.args }
            self.arg_rejected_var = { a : next(self.var_counter) for a in self.args }
        else:
            self.pos_attacks = [ (self.arg_to_int[s], self.arg_to_int[t]) for s,t in pos_attacks ]
            self.neg_attacks = [ (self.arg_to_int[s], self.arg_to_int[t]) for s,t in neg_attacks ]

            self.att_var = { (a,b) : next(self.var_counter) for a in self.args for b in self.args }
            self.var_to_att = { self.att_var[(a,b)] : (a,b) for a in self.args for b in self.args }

            self.pos_cred_enfs = [self.arg_to_int[p] for p in pos_cred_enfs]
            self.neg_cred_enfs = [self.arg_to_int[n] for n in neg_cred_enfs]
            self.pos_skept_enfs = [self.arg_to_int[p] for p in pos_skept_enfs]
            self.neg_skept_enfs = [self.arg_to_int[n] for n in neg_skept_enfs]

            self.pos_conjunct_enfs = [[self.arg_to_int[a] for a in enf_set] for enf_set in pos_conjunct_enfs]
            self.neg_conjunct_enfs = [[self.arg_to_int[a] for a in enf_set] for enf_set in neg_conjunct_enfs]

            self.pos_cred_weight = pos_cred_weight
            self.neg_cred_weight = neg_cred_weight
            self.pos_skept_weight = pos_skept_weight
            self.neg_skept_weight = neg_skept_weight
            self.pos_conjunct_weight = pos_conjunct_weight
            self.neg_conjunct_weight = neg_conjunct_weight

            self.arg_accepted_in_witness_var = { (p,a) : next(self.var_counter) for p in self.pos_cred_enfs for a in self.args }
            self.att_exists_and_source_accepted_in_witness_var = { (p,a,b) : next(self.var_counter) for p in self.pos_cred_enfs for a in self.args for b in self.args }

            self.arg_accepted_in_witness_var |= { (n,a) : next(self.var_counter) for n in self.neg_skept_enfs for a in self.args }
            self.att_exists_and_source_accepted_in_witness_var |= { (n,a,b) : next(self.var_counter) for n in self.neg_skept_enfs for a in self.args for b in self.args }

            self.arg_accepted_in_witness_var |= { (i+len(self.args),a) : next(self.var_counter) for i in range(len(pos_conjunct_enfs)) for a in self.args }
            self.att_exists_and_source_accepted_in_witness_var |= { (i+len(self.args),a,b) : next(self.var_counter) for i in range(len(pos_conjunct_enfs)) for a in self.args for b in self.args }

            self.pos_conjunct_accepted_var = { i : next(self.var_counter) for i in range(len(self.pos_conjunct_enfs)) }
            if self.neg_cred_weight != float("inf"):
                self.neg_cred_target_var = { n : next(self.var_counter) for n in self.neg_cred_enfs }
            if self.pos_skept_weight != float("inf"):
                self.pos_skept_target_var = { p : next(self.var_counter) for p in self.pos_skept_enfs }
            if self.neg_conjunct_weight != float("inf"):
                self.neg_conjunct_var = { i : next(self.var_counter) for i in range(len(self.neg_conjunct_enfs)) }

    def print(self, int_to_arg):
        for a in self.args:
            print('arg(' + str(int_to_arg[a]) + ').')
        for a,b in self.atts:
            print('att(' + str(int_to_arg[a]) + ',' + str(int_to_arg[b]) + ').')

    def print_to_file(self, int_to_arg, filename):
        f = open(filename, "w")
        for a in self.args:
            f.write('arg(' + str(int_to_arg[a]) + ').\n')
        for a,b in self.atts:
            f.write('att(' + str(int_to_arg[a]) + ',' + str(int_to_arg[b]) + ').\n')
        f.close()

def add_arg_rejected_var_clauses(af, formula):
    for a in af.args:
        formula.append([-af.arg_rejected_var[a]] + [af.arg_accepted_var[b] for b in af.attackers[a]])
        for b in af.attackers[a]:
            formula.append([af.arg_rejected_var[a], -af.arg_accepted_var[b]])

def add_cf_clauses(af, formula):
    for a,b in af.atts:
        formula.append([-af.arg_accepted_var[a], -af.arg_accepted_var[b]])

def add_adm_clauses(af, formula):
    add_cf_clauses(af, formula)
    add_arg_rejected_var_clauses(af, formula)
    for a in af.args:
        for b in af.attackers[a]:
            formula.append([-af.arg_accepted_var[a], af.arg_rejected_var[b]])

def add_com_clauses(af, formula):
    add_adm_clauses(af, formula)
    for a in af.args:
        formula.append([af.arg_accepted_var[a]] + [-af.arg_rejected_var[b] for b in af.attackers[a]])

def add_stb_clauses(af, formula):
    add_cf_clauses(af, formula)
    add_arg_rejected_var_clauses(af, formula)
    for a in af.args:
        formula.append([af.arg_accepted_var[a], af.arg_rejected_var[a]])

# TODO: neg conjunct in witness: ensure that conjunctive target is not accepted in any witness
def add_pos_conjunct_accepted_clauses(af, index, formula):
    for a in af.pos_conjunct_enfs[index]:
        formula.append([-af.pos_conjunct_accepted_var[index], af.arg_accepted_in_witness_var[(index + len(af.args), a)]])
    formula.append([af.pos_conjunct_accepted_var[index]] + [-af.arg_accepted_in_witness_var[(index + len(af.args), a)] for a in af.pos_conjunct_enfs[index]])

def add_att_exists_and_source_accepted_in_witness_clauses(af, index, formula):
    for a in af.args:
        for b in af.args:
            formula.append([-af.att_exists_and_source_accepted_in_witness_var[(index,a,b)], af.att_var[(a,b)]])
            formula.append([-af.att_exists_and_source_accepted_in_witness_var[(index,a,b)], af.arg_accepted_in_witness_var[(index,a)]])
            formula.append([af.att_exists_and_source_accepted_in_witness_var[(index,a,b)], -af.att_var[(a,b)], -af.arg_accepted_in_witness_var[(index,a)]])

def add_arg_in_cf_ext_clauses(af, index, formula):
    for a in af.args:
        for b in af.args:
            formula.append([-af.att_var[(a,b)], -af.arg_accepted_in_witness_var[(index, a)], -af.arg_accepted_in_witness_var[(index, b)]])

def add_arg_in_adm_ext_clauses(af, index, formula):
    add_arg_in_cf_ext_clauses(af, index, formula)
    add_att_exists_and_source_accepted_in_witness_clauses(af, index, formula)
    for a in af.args:
        for b in af.args:
            formula.append([-af.att_var[(b,a)], -af.arg_accepted_in_witness_var[(index, a)]]
                           + [af.att_exists_and_source_accepted_in_witness_var[(index, c, b)] for c in af.args])

def add_arg_in_stb_ext_clauses(af, index, formula):
    add_arg_in_cf_ext_clauses(af, index, formula)
    add_att_exists_and_source_accepted_in_witness_clauses(af, index, formula)
    for a in af.args:
        formula.append([af.arg_accepted_in_witness_var[(index, a)]]
                       + [af.att_exists_and_source_accepted_in_witness_var[(index, b, a)] for b in af.args])

def refinement_clause(af, new_af, model=None):
    if model == None:
        return [(-1 if new_af.att_exists[(a,b)] else 1)*af.att_var[(a,b)] for a in af.args for b in af.args]
    else:
        labeling = { a : 0 for a in new_af.args }
        for a in new_af.args:
            if model[new_af.arg_accepted_var[a]-1] > 0:
                labeling[a] = 1
            elif model[new_af.arg_rejected_var[a]-1] > 0:
                labeling[a] = -1
        clause = []
        for a in new_af.args:
            for b in new_af.args:
                if new_af.att_exists[(a,b)]:
                    if labeling[a] == 1 and labeling[b] == -1:
                        clause += [-af.att_var[(a,b)]]
                else:
                    if (labeling[a] == 1 and labeling[b] == 1) or (labeling[a] == 0 and labeling[b] == 1):
                        clause += [af.att_var[(a,b)]]
        return clause

def enforce(af, sem, strong=True):
    assert(af.pos_cred_weight == af.neg_cred_weight == af.pos_skept_weight == af.neg_skept_weight == af.pos_conjunct_weight == af.neg_conjunct_weight == float("inf"))

    formula = WCNF()
    for s,t in af.pos_attacks:
        formula.append([af.att_var[(s,t)]])
    for s,t in af.neg_attacks:
        formula.append([-af.att_var[(s,t)]])

    for p in af.pos_cred_enfs:
        formula.append([af.arg_accepted_in_witness_var[(p, p)]])
        for n in af.neg_cred_enfs:
            formula.append([-af.arg_accepted_in_witness_var[(p, n)]])
        if sem == 'adm' or sem == 'com' or sem == 'prf':
            add_arg_in_adm_ext_clauses(af, p, formula)
        elif sem == 'stb':
             add_arg_in_stb_ext_clauses(af, p, formula)
        else:
             print('Semantics', sem, 'not supported for credulous targets.')
             sys.exit(1)

    for n in af.neg_skept_enfs:
        formula.append([-af.arg_accepted_in_witness_var[(n, n)]])
        for p in af.pos_skept_enfs:
            formula.append([af.arg_accepted_in_witness_var[(n, p)]])
        if sem == 'adm':
            add_arg_in_adm_ext_clauses(af, n, formula)
        elif sem == 'stb':
             add_arg_in_stb_ext_clauses(af, n, formula)
        else:
             print('Semantics', sem, 'not supported for skeptical targets.')
             sys.exit(1)

    for i in range(len(af.pos_conjunct_enfs)):
        add_pos_conjunct_accepted_clauses(af, i, formula)
        formula.append([af.pos_conjunct_accepted_var[i]])
        for n in af.neg_cred_enfs:
            formula.append([-af.arg_accepted_in_witness_var[(i+len(af.args), n)]])
        for p in af.pos_skept_enfs:
            formula.append([af.arg_accepted_in_witness_var[(i+len(af.args), p)]])
        if sem == 'adm' or sem == 'com' or sem == 'prf':
            add_arg_in_adm_ext_clauses(af, i+len(af.args), formula)
        elif sem == 'stb':
            add_arg_in_stb_ext_clauses(af, i+len(af.args), formula)
        else:
            print('Semantics', sem, 'not supported for conjunctive targets.')
            sys.exit(1)

    for a in af.args:
        for b in af.args:
            if af.att_exists[(a,b)]:
                formula.append([af.att_var[(a,b)]], weight=1)
            else:
                formula.append([-af.att_var[(a,b)]], weight=1)
    solver = RC2(formula, solver='g3', adapt=True, exhaust=True, incr=False, minz=True, trim=0, verbose=3)

    count = 0
    while True:
        count += 1
        print("c Iteration", count)

        model = solver.compute()
        if model is None:
            print('s UNSATISFIABLE')
            return None

        new_atts = []
        for a in af.args:
            for b in af.args:
                if model[af.att_var[(a,b)]-1] > 0:
                    new_atts += [(a,b)]
        new_af = AF(af.args, new_atts, static=True)
        print("c Current objective value", solver.cost)

        cnf = CNF()
        if sem == 'adm' or sem == 'com' or sem == 'prf':
            add_adm_clauses(new_af, cnf)
        elif sem == 'stb':
            add_stb_clauses(new_af, cnf)
        sat_solver = Glucose3(bootstrap_with=cnf)

        cex_clause = [new_af.arg_accepted_var[n] for n in af.neg_cred_enfs]
        cex_clause += [-new_af.arg_accepted_var[p] for p in af.pos_skept_enfs]
        for i in range(len(af.neg_conjunct_enfs)):
            var = next(new_af.var_counter)
            for a in af.neg_conjunct_enfs[i]:
                sat_solver.add_clause([-var, new_af.arg_accepted_var[a]])
            sat_solver.add_clause([var] + [-new_af.arg_accepted_var[a] for a in af.neg_conjunct_enfs[i]])
            cex_clause.append(var)
        sat_solver.add_clause(cex_clause)

        result = sat_solver.solve()
        if result == True:
            clause = refinement_clause(af, new_af, sat_solver.get_model() if strong else None)
            solver.add_clause(clause)
        else:
            print("c RC2 oracle time:", round(solver.oracle_time(),2), "seconds")
            print('c Number of iterations:', count)
            print('s OPTIMUM FOUND')
            print('o {0}'.format(solver.cost))
            return new_af

def enforce_with_soft_targets_lex(af, sem, strong=True):
    formula = WCNF()
    for s,t in af.pos_attacks:
        formula.append([af.att_var[(s,t)]])
    for s,t in af.neg_attacks:
        formula.append([-af.att_var[(s,t)]])

    for p in af.pos_cred_enfs:
        if af.pos_cred_weight == float("inf"):
            formula.append([af.arg_accepted_in_witness_var[(p, p)]])
        if af.neg_cred_weight == float("inf"):
            for n in af.neg_cred_enfs:
                formula.append([-af.arg_accepted_in_witness_var[(p, n)]])
        else:
            for n in af.neg_cred_enfs:
                formula.append([-af.neg_cred_target_var[n], -af.arg_accepted_in_witness_var[(p, n)]])
        if sem == 'adm' or sem == 'com' or sem == 'prf':
            add_arg_in_adm_ext_clauses(af, p, formula)
        elif sem == 'stb':
            add_arg_in_stb_ext_clauses(af, p, formula)
        else:
            print('Semantics', sem, 'not supported for credulous targets.')
            sys.exit(1)

    for n in af.neg_skept_enfs:
        if af.neg_skept_weight == float("inf"):
            formula.append([-af.arg_accepted_in_witness_var[(n, n)]])
        if af.pos_skept_weight == float("inf"):
            for p in af.pos_skept_enfs:
                formula.append([af.arg_accepted_in_witness_var[(n, p)]])
        if sem == 'adm':
            add_arg_in_adm_ext_clauses(af, n, formula)
        elif sem == 'stb':
             add_arg_in_stb_ext_clauses(af, n, formula)
        else:
             print('Semantics', sem, 'not supported for skeptical targets.')
             sys.exit(1)

    for i in range(len(af.pos_conjunct_enfs)):
        add_pos_conjunct_accepted_clauses(af, i, formula)
        if af.pos_conjunct_weight == float("inf"):
            formula.append([af.pos_conjunct_accepted_var[i]])
        if af.neg_cred_weight == float("inf"):
            for n in af.neg_cred_enfs:
                formula.append([-af.arg_accepted_in_witness_var[(i+len(af.args), n)]])
        else:
            for n in af.neg_cred_enfs:
                formula.append([-af.neg_cred_target_var[n], -af.arg_accepted_in_witness_var[(i+len(af.args), n)]])
        if af.pos_skept_weight == float("inf"):
            for p in af.pos_skept_enfs:
                formula.append([af.arg_accepted_in_witness_var[(i+len(af.args), p)]])
        else:
            for p in af.pos_skept_enfs:
                formula.append([-af.pos_skept_target_var[p], af.arg_accepted_in_witness_var[(i+len(af.args), p)]])
        if sem == 'adm' or sem == 'com' or sem == 'prf':
            add_arg_in_adm_ext_clauses(af, i+len(af.args), formula)
        elif sem == 'stb':
            add_arg_in_stb_ext_clauses(af, i+len(af.args), formula)
        else:
            print('Semantics', sem, 'not supported.')
            sys.exit(1)

    target_lits = []
    target_solver = RC2(formula, solver='g3', adapt=True, exhaust=True, incr=False, trim=0, minz=True, verbose=3)

    if af.pos_cred_weight != float("inf"):
        for p in af.pos_cred_enfs:
            target_solver.add_clause([af.arg_accepted_in_witness_var[(p, p)]], weight=af.pos_cred_weight)
            target_lits.append(af.arg_accepted_in_witness_var[(p, p)])

    if af.neg_cred_weight != float("inf"):
        for n in af.neg_cred_enfs:
            target_solver.add_clause([af.neg_cred_target_var[n]], weight=af.neg_cred_weight)
            target_lits.append(af.neg_cred_target_var[n])

    if af.pos_skept_weight != float("inf"):
        for p in af.pos_skept_enfs:
            target_solver.add_clause([af.pos_skept_target_var[p]], weight=af.pos_skept_weight)
            target_lits.append(af.pos_skept_target_var[p])

    if af.neg_skept_weight != float("inf"):
        for n in af.neg_cred_enfs:
            target_solver.add_clause([-af.arg_accepted_in_witness_var[(n, n)]], weight=af.neg_skept_weight)
            target_lits.append(-af.arg_accepted_in_witness_var[(n, n)])

    if af.pos_conjunct_weight != float("inf"):
        for i in range(len(af.pos_conjunct_enfs)):
            target_solver.add_clause([af.pos_conjunct_accepted_var[i]], weight=af.pos_conjunct_weight)
            target_lits.append(af.pos_conjunct_accepted_var[i])

    if af.neg_conjunct_weight != float("inf"):
        for i in range(len(af.neg_conjunct_enfs)):
            target_solver.add_clause([af.neg_conjunct_var[i]], weight=af.neg_conjunct_weight)
            target_lits.append(af.neg_conjunct_var[i])

    print("targets", target_lits)
    top = next(af.var_counter)-1

    count = 0
    while True:
        count += 1
        print("c Iteration", count)

        model = target_solver.compute()
        if model is None:
            print('s UNSATISFIABLE (target)')
            return None

        new_atts = []
        for a in af.args:
            for b in af.args:
                if model[af.att_var[(a,b)]-1] > 0:
                    new_atts += [(a,b)]
        new_af = AF(af.args, new_atts, static=True)
        print("c Current objective value (targets)", target_solver.cost)
        print("c Number of attacks", len(new_atts))

        print("c Computing syntactic change")
        change_solver = RC2(formula, solver='g3', adapt=True, exhaust=True, incr=False, trim=0, minz=True, verbose=3)
        card = CardEnc.atmost([-lit for lit in target_lits], bound=target_solver.cost, top_id=top, encoding=CARD_ENCODING)
        # TODO: PB constraint for weighted instances
        for clause in card:
            change_solver.add_clause(clause)
        for a in af.args:
            for b in af.args:
                if af.att_exists[(a,b)]:
                    change_solver.add_clause([af.att_var[(a,b)]], weight=1)
                else:
                    change_solver.add_clause([-af.att_var[(a,b)]], weight=1)

        while True:
            model = change_solver.compute()
            if model is None:
                print('s UNSATISFIABLE (change)')
                break

            new_atts = []
            for a in af.args:
                for b in af.args:
                    if model[af.att_var[(a,b)]-1] > 0:
                        new_atts += [(a,b)]
            new_af = AF(af.args, new_atts, static=True)
            print("c Current objective value (changes)", change_solver.cost)
            print("c Number of attacks", len(new_atts))

            cnf = CNF()
            if sem == 'adm' or sem == 'com' or sem == 'prf':
                add_adm_clauses(new_af, cnf)
            elif sem == 'stb':
                add_stb_clauses(new_af, cnf)
            sat_solver = Glucose3(bootstrap_with=cnf)

            cex_clause = []
            if af.neg_cred_weight == float("inf"):
                cex_clause = [new_af.arg_accepted_var[n] for n in af.neg_cred_enfs]
            else:
                for n in af.neg_cred_enfs:
                    if model[af.neg_cred_target_var[n]-1] > 0:
                        cex_clause.append(new_af.arg_accepted_var[n])
            if af.pos_skept_weight == float("inf"):
                cex_clause += [-new_af.arg_accepted_var[p] for p in af.pos_skept_enfs]
            else:
                for p in af.pos_skept_enfs:
                    if model[af.pos_skept_target_var[p]-1] > 0:
                        cex_clause.append(-new_af.arg_accepted_var[p])
            conjunct_var = { i : 0 for i in range(len(af.neg_conjunct_enfs)) }
            for i in range(len(af.neg_conjunct_enfs)):
                if af.neg_conjunct_weight == float("inf") or model[af.neg_conjunct_var[i]-1] > 0:
                    var = next(new_af.var_counter)
                    for a in af.neg_conjunct_enfs[i]:
                        sat_solver.add_clause([-var, new_af.arg_accepted_var[a]])
                    sat_solver.add_clause([var] + [-new_af.arg_accepted_var[a] for a in af.neg_conjunct_enfs[i]])
                    cex_clause.append(var)
                    conjunct_var[i] = var
            sat_solver.add_clause(cex_clause)

            result = sat_solver.solve()
            if result == True:
                print("c Counterexample found (changes)")
                sat_model = sat_solver.get_model()
                clause = refinement_clause(af, new_af, sat_model if strong else None)
                flag = False
                if af.neg_cred_weight == float("inf"):
                    for n in af.neg_cred_enfs:
                        if sat_model[new_af.arg_accepted_var[n]-1] > 0:
                            target_solver.add_clause(clause)
                            change_solver.add_clause(clause)
                            formula.append(clause)
                            flag = True
                            print("c Added hard refinement for negative credulous targets")
                            break
                if flag:
                    continue
                if af.pos_skept_weight == float("inf"):
                    for p in af.pos_skept_enfs:
                        if sat_model[new_af.arg_accepted_var[p]-1] < 0:
                            target_solver.add_clause(clause)
                            change_solver.add_clause(clause)
                            formula.append(clause)
                            flag = True
                            print("c Added hard refinement for positive skeptical targets")
                            break
                if flag:
                    continue
                if af.neg_conjunct_weight == float("inf"):
                    for n in af.neg_conjunct_enfs:
                        if sat_model[conjunct_var[i]-1] > 0:
                            target_solver.add_clause(clause)
                            change_solver.add_clause(clause)
                            formula.append(clause)
                            flag = True
                            print("c Added hard refinement for negative conjunctive targets")
                            break
                if flag:
                    continue
                for n in af.neg_cred_enfs:
                    if af.neg_cred_weight != float("inf") and model[af.neg_cred_target_var[n]-1] > 0:
                        if sat_model[new_af.arg_accepted_var[n]-1] > 0:
                            target_solver.add_clause([-af.neg_cred_target_var[n]] + clause)
                            change_solver.add_clause([-af.neg_cred_target_var[n]] + clause)
                            formula.append([-af.neg_cred_target_var[n]] + clause)
                            print("c Added soft refinement for negative credulous targets")
                for p in af.pos_skept_enfs:
                    if af.pos_skept_weight != float("inf") and model[af.pos_skept_target_var[p]-1] > 0:
                        if sat_model[new_af.arg_accepted_var[p]-1] < 0:
                            target_solver.add_clause([-af.pos_skept_target_var[p]] + clause)
                            change_solver.add_clause([-af.pos_skept_target_var[p]] + clause)
                            formula.append([-af.pos_skept_target_var[p]] + clause)
                            print("c Added soft refinement for positive skeptical targets")
                for i in range(len(af.neg_conjunct_enfs)):
                    if af.neg_conjunct_weight != float("inf") and model[af.neg_conjunct_var[i]-1] > 0:
                        if sat_model[conjunct_var[i]-1] > 0:
                            target_solver.add_clause([-af.neg_conjunct_var[i]] + clause)
                            change_solver.add_clause([-af.neg_conjunct_var[i]] + clause)
                            formula.append([-af.neg_conjunct_var[i]] + clause)
                            print("c Added soft refinement for negative conjunctive targets")
                continue

            print('c Number of iterations:', count)
            print('s OPTIMUM FOUND')
            print('o {0} {1}'.format(target_solver.cost, change_solver.cost))
            return new_af

def enforce_with_soft_targets_wght(af, sem, strong=True):
    formula = WCNF()
    for s,t in af.pos_attacks:
        formula.append([af.att_var[(s,t)]])
    for s,t in af.neg_attacks:
        formula.append([-af.att_var[(s,t)]])

    for p in af.pos_cred_enfs:
        if af.pos_cred_weight == float("inf"):
            formula.append([af.arg_accepted_in_witness_var[(p, p)]])
        if af.neg_cred_weight == float("inf"):
            for n in af.neg_cred_enfs:
                formula.append([-af.arg_accepted_in_witness_var[(p, n)]])
        else:
            for n in af.neg_cred_enfs:
                formula.append([-af.neg_cred_target_var[n], -af.arg_accepted_in_witness_var[(p, n)]])
        if sem == 'adm' or sem == 'com' or sem == 'prf':
            add_arg_in_adm_ext_clauses(af, p, formula)
        elif sem == 'stb':
            add_arg_in_stb_ext_clauses(af, p, formula)
        else:
            print('Semantics', sem, 'not supported for credulous targets.')
            sys.exit(1)

    for n in af.neg_skept_enfs:
        if af.neg_skept_weight == float("inf"):
            formula.append([-af.arg_accepted_in_witness_var[(n, n)]])
        if af.pos_skept_weight == float("inf"):
            for p in af.pos_skept_enfs:
                formula.append([af.arg_accepted_in_witness_var[(n, p)]])
        if sem == 'adm':
            add_arg_in_adm_ext_clauses(af, n, formula)
        elif sem == 'stb':
             add_arg_in_stb_ext_clauses(af, n, formula)
        else:
             print('Semantics', sem, 'not supported for skeptical targets.')
             sys.exit(1)

    for i in range(len(af.pos_conjunct_enfs)):
        add_pos_conjunct_accepted_clauses(af, i, formula)
        if af.pos_conjunct_weight == float("inf"):
            formula.append([af.pos_conjunct_accepted_var[i]])
        if af.neg_cred_weight == float("inf"):
            for n in af.neg_cred_enfs:
                formula.append([-af.arg_accepted_in_witness_var[(i+len(af.args), n)]])
        else:
            for n in af.neg_cred_enfs:
                formula.append([-af.neg_cred_target_var[n], -af.arg_accepted_in_witness_var[(i+len(af.args), n)]])
        if af.pos_skept_weight == float("inf"):
            for p in af.pos_skept_enfs:
                formula.append([af.arg_accepted_in_witness_var[(i+len(af.args), p)]])
        else:
            for p in af.pos_skept_enfs:
                formula.append([-af.pos_skept_target_var[p], af.arg_accepted_in_witness_var[(i+len(af.args), p)]])
        if sem == 'adm' or sem == 'com' or sem == 'prf':
            add_arg_in_adm_ext_clauses(af, i+len(af.args), formula)
        elif sem == 'stb':
            add_arg_in_stb_ext_clauses(af, i+len(af.args), formula)
        else:
            print('Semantics', sem, 'not supported.')
            sys.exit(1)

    target_lits = []

    weight_coeff = len(af.args)*len(af.args)+1
    if af.pos_cred_weight != float("inf"):
        for p in af.pos_cred_enfs:
            formula.append([af.arg_accepted_in_witness_var[(p, p)]], weight=af.pos_cred_weight*weight_coeff)
            target_lits.append(af.arg_accepted_in_witness_var[(p, p)])

    if af.neg_cred_weight != float("inf"):
        for n in af.neg_cred_enfs:
            formula.append([af.neg_cred_target_var[n]], weight=af.neg_cred_weight*weight_coeff)
            target_lits.append(af.neg_cred_target_var[n])

    if af.pos_skept_weight != float("inf"):
        for p in af.pos_skept_enfs:
            target_solver.add_clause([af.pos_skept_target_var[p]], weight=af.pos_skept_weight)
            target_lits.append(af.pos_skept_target_var[p])

    if af.neg_skept_weight != float("inf"):
        for n in af.neg_cred_enfs:
            target_solver.add_clause([-af.arg_accepted_in_witness_var[(n, n)]], weight=af.neg_skept_weight)
            target_lits.append(-af.arg_accepted_in_witness_var[(n, n)])

    if af.pos_conjunct_weight != float("inf"):
        for i in range(len(af.pos_conjunct_enfs)):
            formula.append([af.pos_conjunct_accepted_var[i]], weight=af.pos_conjunct_weight*weight_coeff)
            target_lits.append(af.pos_conjunct_accepted_var[i])

    if af.neg_conjunct_weight != float("inf"):
        for i in range(len(af.neg_conjunct_enfs)):
            formula.append([af.neg_conjunct_var[i]], weight=af.neg_conjunct_weight*weight_coeff)
            target_lits.append(af.neg_conjunct_var[i])

    print("targets", target_lits)
    for a in af.args:
        for b in af.args:
            if af.att_exists[(a,b)]:
                formula.append([af.att_var[(a,b)]], weight=1)
            else:
                formula.append([-af.att_var[(a,b)]], weight=1)

    solver = RC2Stratified(formula, solver='g3', adapt=True, blo="div", exhaust=True, incr=False, trim=0, minz=True, nohard=True, verbose=3)
    #solver = RC2Stratified(formula, solver='g3', adapt=True, blo="div", exhaust=True, incr=False, minz=False, trim=5, nohard=True, verbose=3)

    count = 0
    while True:
        count += 1
        print("c Iteration", count)

        model = solver.compute()
        if model is None:
            print('s UNSATISFIABLE')
            return None

        new_atts = []
        for a in af.args:
            for b in af.args:
                if model[af.att_var[(a,b)]-1] > 0:
                    new_atts += [(a,b)]
        new_af = AF(af.args, new_atts, static=True)
        print("c Current objective value", solver.cost)
        print("c Number of attacks", len(new_atts))

        cnf = CNF()
        if sem == 'adm' or sem == 'com' or sem == 'prf':
            add_adm_clauses(new_af, cnf)
        elif sem == 'stb':
            add_stb_clauses(new_af, cnf)
        sat_solver = Glucose3(bootstrap_with=cnf)

        cex_clause = []
        if af.neg_cred_weight == float("inf"):
            cex_clause = [new_af.arg_accepted_var[n] for n in af.neg_cred_enfs]
        else:
            for n in af.neg_cred_enfs:
                if model[af.neg_cred_target_var[n]-1] > 0:
                    cex_clause.append(new_af.arg_accepted_var[n])

        if af.pos_skept_weight == float("inf"):
            cex_clause += [-new_af.arg_accepted_var[p] for p in af.pos_skept_enfs]
        else:
            for p in af.pos_skept_enfs:
                if model[af.pos_skept_target_var[p]-1] > 0:
                    cex_clause.append(-new_af.arg_accepted_var[p])

        conjunct_var = { i : 0 for i in range(len(af.neg_conjunct_enfs)) }
        for i in range(len(af.neg_conjunct_enfs)):
            if af.neg_conjunct_weight == float("inf") or model[af.neg_conjunct_var[i]-1] > 0:
                var = next(new_af.var_counter)
                for a in af.neg_conjunct_enfs[i]:
                    sat_solver.add_clause([-var, new_af.arg_accepted_var[a]])
                sat_solver.add_clause([var] + [-new_af.arg_accepted_var[a] for a in af.neg_conjunct_enfs[i]])
                cex_clause.append(var)
                conjunct_var[i] = var
        sat_solver.add_clause(cex_clause)

        result = sat_solver.solve()
        if result == True:
            print("c Counterexample found")
            sat_model = sat_solver.get_model()
            clause = refinement_clause(af, new_af, sat_model if strong else None)
            flag = False
            if af.neg_cred_weight == float("inf"):
                for n in af.neg_cred_enfs:
                    if sat_model[new_af.arg_accepted_var[n]-1] > 0:
                        solver.add_clause(clause)
                        flag = True
                        print("c Added hard refinement for negative credulous targets")
                        break
            if flag:
                continue
            if af.pos_skept_weight == float("inf"):
                for p in af.pos_skept_enfs:
                    if sat_model[new_af.arg_accepted_var[p]-1] < 0:
                        solver.add_clause(clause)
                        flag = True
                        print("c Added hard refinement for positive skeptical targets")
                        break
            if flag:
                continue
            if af.neg_conjunct_weight == float("inf"):
                for n in af.neg_conjunct_enfs:
                    if sat_model[conjunct_var[i]-1] > 0:
                        solver.add_clause(clause)
                        flag = True
                        print("c Added hard refinement for negative conjunctive targets")
                        break
            if flag:
                continue
            for n in af.neg_cred_enfs:
                if af.neg_cred_weight != float("inf") and model[af.neg_cred_target_var[n]-1] > 0:
                    if sat_model[new_af.arg_accepted_var[n]-1] > 0:
                        solver.add_clause([-af.neg_cred_target_var[n]] + clause)
                        print("c Added soft refinement for negative credulous targets")
            for p in af.pos_skept_enfs:
                if af.pos_skept_weight != float("inf") and model[af.pos_skept_target_var[p]-1] > 0:
                    if sat_model[new_af.arg_accepted_var[p]-1] < 0:
                        solver.add_clause([-af.pos_skept_target_var[p]] + clause)
                        print("c Added soft refinement for positive skeptical targets")
            for i in range(len(af.neg_conjunct_enfs)):
                if af.neg_conjunct_weight != float("inf") and model[af.neg_conjunct_var[i]-1] > 0:
                    if sat_model[conjunct_var[i]-1] > 0:
                        solver.add_clause([-af.neg_conjunct_var[i]] + clause)
                        print("c Added soft refinement for negative conjunctive targets")
            continue

        print('c Number of iterations:', count)
        print('s OPTIMUM FOUND')
        print('o {0}'.format(solver.cost))
        return new_af

def parse_af(filename):
    lines = open(filename, 'r').read().split('\n')
    args = [line.replace('arg(', '').replace(').', '') for line in lines if line.startswith('arg')]
    atts = [line.replace('att(', '').replace(').', '').split(',') for line in lines if line.startswith('att')]
    return args, atts

def parse_query(filename):
    lines = open(filename, 'r').read().split('\n')
    target_lines = [line.replace('target(', '').replace(').', '').split(',') for line in lines if line.startswith('target')]
    neg_target_lines = [line.replace('neg_target(', '').replace(').', '').split(',') for line in lines if line.startswith('neg_target')]
    assert(len(target_lines) <= 1 and len(neg_target_lines) <= 1)
    target = neg_target = []
    if len(target_lines) > 0:
        target = target_lines[0]
    if len(neg_target_lines) > 0:
        neg_target = neg_target_lines[0]
    pos_conjuncts = [line.replace('pos_conjunct(', '').replace(').', '').split(',') for line in lines if line.startswith('pos_conjunct')]
    neg_conjuncts = [line.replace('neg_conjunct(', '').replace(').', '').split(',') for line in lines if line.startswith('neg_conjunct')]
    return target, neg_target, pos_conjuncts, neg_conjuncts

def parse_cons(filename):
    lines = open(filename, 'r').read().split('\n')
    atts = [line.replace('att(', '').replace(').', '').split(',') for line in lines if line.startswith('att')]
    neg_atts = [line.replace('-att(', '').replace(').', '').split(',') for line in lines if line.startswith('-att')]
    return atts, neg_atts

def get_cred_accepted_arguments(af, sem):
    sat_solver = Glucose3()
    cnf = CNF()
    if sem == 'adm' or sem == 'com' or sem == 'prf':
        add_adm_clauses(af, cnf)
    elif sem == 'stb':
        add_stb_clauses(af, cnf)
    sat_solver = Glucose3(bootstrap_with=cnf)
    accepted = set()
    while True:
        clause = [ af.arg_accepted_var[a] for a in af.args if a not in accepted ]
        sat_solver.add_clause(clause)
        result = sat_solver.solve()
        if result == False:
            break
        model = sat_solver.get_model()
        extension = [ a for a in af.args if model[af.arg_accepted_var[a]-1] > 0 ]
        accepted.update(extension)
    sat_solver.delete()
    return accepted

def get_skept_accepted_arguments(af, sem):
    sat_solver = Glucose3()
    cnf = CNF()
    if sem == 'adm':
        add_adm_clauses(af, cnf)
    elif sem == 'com':
        add_com_clauses(af, cnf)
    elif sem == 'stb':
        add_stb_clauses(af, cnf)
    sat_solver = Glucose3(bootstrap_with=cnf)
    not_accepted = set()
    while True:
        clause = [ -af.arg_accepted_var[a] for a in af.args if a not in not_accepted ]
        sat_solver.add_clause(clause)
        result = sat_solver.solve()
        if result == False:
            break
        model = sat_solver.get_model()
        not_extension = [ a for a in af.args if model[af.arg_accepted_var[a]-1] < 0 ]
        not_accepted.update(not_extension)
    sat_solver.delete()
    return set([a for a in af.args if a not in not_accepted])

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description="Generalized Enforcement")
    parser.add_argument("af", help="Input filename for AF instance.")
    parser.add_argument("query", help="Input filename for enforcement query.")
    parser.add_argument("cons", help="Input filename for constraints.", nargs='?', default=None)
    parser.add_argument("--semantics", choices=["adm", "com", "stb"], default="stb", help="Argumentation semantics")
    parser.add_argument("--mode", choices=["cred", "skept"], default="cred", help="Reasoning mode (cred or skept).")
    parser.add_argument("--verbose", default=False, action="store_true", help="Verbose output")
    parser.add_argument("--pos-cred-weight", default="inf", help="Weight for positive credulous targets (default: inf).")
    parser.add_argument("--neg-cred-weight", default="inf", help="Weight for negative credulous targets (default: inf).")
    parser.add_argument("--pos-skept-weight", default="inf", help="Weight for positive skeptical targets (default: inf).")
    parser.add_argument("--neg-skept-weight", default="inf", help="Weight for negative skeptical targets (default: inf).")
    parser.add_argument("--pos-conjunct-weight", default="inf", help="Weight for positive conjunctive targets (default: inf).")
    parser.add_argument("--neg-conjunct-weight", default="inf", help="Weight for negative conjunctive targets (default: inf).")
    parser.add_argument("--semantic-targets", default=False, action="store_true", help="Modify non-conjunctive targets to take accepted arguments into account.")
    args = parser.parse_args()

    start_time = get_utime()

    arguments, attacks = parse_af(args.af)
    target, neg_target, pos_conjuncts, neg_conjuncts = parse_query(args.query)
    pos_attacks = []
    neg_attacks = []
    if args.cons:
        pos_attacks, neg_attacks = parse_cons(args.cons)

    if args.semantic_targets and args.mode == "cred":
        print("c Computing the set of credulously accepted arguments...")
        static_af = AF(arguments, attacks, semantics=args.semantics, static=True)
        accepted = get_cred_accepted_arguments(static_af, args.semantics)
        if args.verbose:
            print("c", accepted)
        accepted = set(static_af.int_to_arg[a] for a in accepted)

        init_time = get_utime()
        print("c Accepted time:", round(init_time-start_time, 2), "seconds")

        target_set = set(target)
        neg_target_set = set(neg_target)
        target_set.update(accepted.difference(set(neg_target)))
        neg_target_set.update(set(arguments).difference(accepted.union(set(target))))
        target = sorted(list(target_set))
        neg_target = sorted(list(neg_target_set))
        if args.verbose:
            print("c Modified positive target:", target)
            print("c Modified negative target:", neg_target)

    if args.semantic_targets and args.mode == "skept":
        print("c Computing the set of skeptically arguments...")
        static_af = AF(arguments, attacks, semantics=args.semantics, static=True)
        accepted = get_skept_accepted_arguments(static_af, args.semantics)
        if args.verbose:
            print("c", accepted)
        accepted = set(static_af.int_to_arg[a] for a in accepted)

        init_time = get_utime()
        print("c Accepted time:", round(init_time-start_time, 2), "seconds")

        target_set = set(target)
        neg_target_set = set(neg_target)
        target_set.update(accepted.difference(set(neg_target)))
        neg_target_set.update(set(arguments).difference(accepted.union(set(target))))
        target = sorted(list(target_set))
        neg_target = sorted(list(neg_target_set))
        if args.verbose:
            print("c Modified positive target:", target)
            print("c Modified negative target:", neg_target)

    pos_cred_weight = float("inf")
    neg_cred_weight = float("inf")
    pos_skept_weight = float("inf")
    neg_skept_weight = float("inf")
    pos_conjunct_weight = float("inf")
    neg_conjunct_weight = float("inf")
    if args.pos_cred_weight != "inf":
        pos_cred_weight = int(args.pos_cred_weight)
    if args.neg_cred_weight != "inf":
        neg_cred_weight = int(args.neg_cred_weight)
    if args.pos_skept_weight != "inf":
        pos_skept_weight = int(args.pos_skept_weight)
    if args.neg_skept_weight != "inf":
        neg_skept_weight = int(args.neg_skept_weight)
    if args.pos_conjunct_weight != "inf":
        pos_conjunct_weight = int(args.pos_conjunct_weight)
    if args.neg_conjunct_weight != "inf":
        neg_conjunct_weight = int(args.neg_conjunct_weight)

    print("c Computing enforcement...")
    start_enf_time = get_utime()
    if args.mode == "cred":
        enforcement_instance = AF(arguments, attacks, args.semantics, target, neg_target, [], [], pos_conjuncts, neg_conjuncts,
            pos_cred_weight, neg_cred_weight, pos_skept_weight, neg_skept_weight, pos_conjunct_weight, neg_conjunct_weight, pos_attacks, neg_attacks)
    elif args.mode == "skept":
        enforcement_instance = AF(arguments, attacks, args.semantics, [], [], target, neg_target, pos_conjuncts, neg_conjuncts,
            pos_cred_weight, neg_cred_weight, pos_skept_weight, neg_skept_weight, pos_conjunct_weight, neg_conjunct_weight, pos_attacks, neg_attacks)

    if pos_cred_weight == neg_cred_weight == pos_skept_weight == neg_skept_weight == pos_conjunct_weight == neg_conjunct_weight == float("inf"):
        print("c No soft targets: minimizing syntactic distance")
        new_af = enforce(enforcement_instance, args.semantics)
    else:
        print("c Soft targets detected: lexicographically minimizing target satisfaction and distance")
        new_af = enforce_with_soft_targets_wght(enforcement_instance, args.semantics)

    end_enf_time = get_utime()
    print("c Enforcement time:", round(end_enf_time-start_enf_time,2), "seconds")
    if new_af is not None and args.verbose:
        new_af.print(enforcement_instance.int_to_arg)
        if args.mode == "cred":
            accepted = get_cred_accepted_arguments(new_af, args.semantics)
            accepted = set(enforcement_instance.int_to_arg[a] for a in accepted)
            print(sorted(list(accepted)))
        elif args.mode == "skept":
            accepted = get_skept_accepted_arguments(new_af, args.semantics)
            accepted = set(enforcement_instance.int_to_arg[a] for a in accepted)
            print(sorted(list(accepted)))

#    filename = sys.argv[1]
#    semantics = sys.argv[2]
#    solver = RC2(WCNF())
#    if semantics not in ['adm', 'com', 'prf', 'stb']:
#        print('Semantics', semantics, 'not supported.')
#        sys.exit(1)
#    args, atts, pos_enfs, neg_enfs, join_enfs, sept_enfs = parse_af_and_enfs(filename, mode)
#    af = AF(args, atts, semantics, pos_enfs, neg_enfs, join_enfs, sept_enfs)
#    enforce(af, semantics, solver).print(af.int_to_arg)

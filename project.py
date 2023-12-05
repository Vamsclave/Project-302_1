from utils import *
from tests import *

from automata.fa.fa import FA
from automata.fa.dfa import DFA
from automata.fa.nfa import NFA
from itertools import product
import copy
from pysat.solvers import Minisat22, Minicard
from pysat.formula import CNF, CNFPlus, IDPool

# Q2
def P_clauses(cnf, vpool, k, P):
    for word in P:
        nodes_list = [([0],word)]
        finished_node = []
        while len(nodes_list) != 0:
            start_node = nodes_list.pop(0)
            if len(start_node[1]) != 0 :
                new_alpha = start_node[1][1:]
                for i in range(k):
                    node = list(start_node[0])
                    node.append(i)
                    nodes_list.append((node , new_alpha))
            else:
                finished_node.append(start_node[0])
        compiled_node = []
        for possibility in finished_node:
            poss = set()
            for i in range(len(word)):
                if vpool.id(f"etat{possibility[i]}_to_etat{possibility[i+1]}_with_{word[i]}") not in poss:
                    poss.add(vpool.id(f"etat{possibility[i]}_to_etat{possibility[i+1]}_with_{word[i]}"))
            poss.add(vpool.id(f"etat{possibility[len(word)]}_is_final"))
            if poss not in compiled_node:
              compiled_node.append(poss)
        for possibility in product(*compiled_node):
            cnf.append(list(possibility))
def N_clauses(cnf, vpool, k, N):
    for word in N:
        nodes_list = [([0],word)]
        finished_node = []
        while len(nodes_list) != 0:
            start_node = nodes_list.pop(0)
            if len(start_node[1]) != 0 :
                new_alpha = start_node[1][1:]
                for i in range(k):
                    node = list(start_node[0])
                    node.append(i)
                    nodes_list.append((node , new_alpha))
            else:
                finished_node.append(start_node[0])
        # not possibility AND  possibility  AND ... AND not possibility
        for possibility in finished_node:
            #  not t(q0,qi,a) OR not t(qi,qj,b) OR .... OR not F(qk)
            ORClause = []
            for i in range(len(word)):
                ORClause.append(-vpool.id(f"etat{possibility[i]}_to_etat{possibility[i+1]}_with_{word[i]}"))
            ORClause.append(-vpool.id(f"etat{possibility[len(word)]}_is_final"))
            cnf.append(ORClause)
        # adding clause for each word
def Basic_clauses(cnf, vpool, k, alphabet, P, N):
    cnf.append([vpool.id("etat0")])
    # F(qi) -> qi
    for i in range(1, k):
        cnf.append([-vpool.id(f"etat{i}_is_final"), vpool.id(f"etat{i}")])
    # t(qi,qj,a) -> (qi AND qj)
    for i in range(k):
        for j in range(k):
            for letter in alphabet:
                # (AND all letter(-t(qi,qj,a) AND -t(qj,qi,a))) V (qi AND qj)
                ORCLAUSE = []
                # (qi and qj)
                ORCLAUSE.append(vpool.id(f"etat{i}"))
                ORCLAUSE.append(-vpool.id(f"etat{i}_to_etat{j}_with_{letter}"))
                cnf.append(ORCLAUSE)
                ORCLAUSE.clear()
                ORCLAUSE.append(vpool.id(f"etat{j}"))
                ORCLAUSE.append(-vpool.id(f"etat{i}_to_etat{j}_with_{letter}"))
                cnf.append(ORCLAUSE)
    # t(qi,qj,a) -> (AND all k!=j -t(qi,qk,a))
    for i in range(k):
        for j in range(k):
            for letter in alphabet:
                for l in range(k):
                    if l != j:
                        ORCLAUSE = []
                        ORCLAUSE.append(-vpool.id(f"etat{i}_to_etat{j}_with_{letter}"))
                        ORCLAUSE.append(-vpool.id(f"etat{i}_to_etat{l}_with_{letter}"))
                        cnf.append(ORCLAUSE)
    print("basic clause adding")
    N_clauses(cnf, vpool, k, N)
    print("N adding")
    P_clauses(cnf, vpool, k, P)
    print("P adding")
def create_automate(model, vpool, alphabet, k):
    variable_values = dict()
    for literal in model:
        variable = abs(literal)
        value = literal > 0
        variable_name = vpool.obj(variable)  # Convert variable ID back to name
        variable_values[variable_name] = value
    states = set()
    states.add("q0")
    for i in range(1,k):
        if variable_values[f"etat{i}"]:
            states.add(f"q{i}")
    transitions = dict()
    for i in range(k):
        for j in range(k):
            for letter in alphabet:
                if variable_values[f"etat{i}_to_etat{j}_with_{letter}"]:
                    if f"q{i}" in transitions:
                        transitions[f"q{i}"][letter] = f"q{j}"
                    else:
                        transitions[f"q{i}"] = {letter:f"q{j}"}
    finals = set()
    for i in range(k):
        if variable_values[f"etat{i}_is_final"]:
            finals.add(f"q{i}")
    automaton = DFA(
        states=states,
        input_symbols={char for char in alphabet},
        transitions=transitions,
        initial_state='q0',
        final_states=finals,
    )
    return automaton

def gen_aut(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    vpool = IDPool()
    cnf = CNF()
    for i in range(k):
        vpool.id(f"etat{i}")# create k state form 0 to k-1
        vpool.id(f"etat{i}_is_final")# create booleen to express if a state is final
        for j in range(k):
            for letter in alphabet:
                vpool.id(f"etat{i}_to_etat{j}_with_{letter}")# create a possible link with each state
    print("variable created")
    Basic_clauses(cnf, vpool, k, alphabet, pos, neg)
    # Create a SAT solver
    print("basic litteral created")
    solver = Minisat22()

    # Add clauses to the solver
    for clause in cnf:
        solver.add_clause(clause)
    print("litteral added to solver")
    # Solve the SAT problem
    if solver.solve():
        model = solver.get_model()
        automate = create_automate(model, vpool, alphabet, k)
        show_automaton(automate)
        print("automate created")
        return automate

# Q3
def minimal_node_clauses(cnf, vpool, k, alphabet):
        ORCLAUSE = []
        for i in range(1,k):
            ORCLAUSE.append(-vpool.id(f"etat{i}"))
            for j in range(k):
                for letter in alphabet:
                    ORCLAUSE.append(vpool.id(f"etat{j}_to_etat{i}_with_{letter}"))
            cnf.append(ORCLAUSE)

def gen_minaut(alphabet: str, pos: list[str], neg: list[str]) -> DFA:
    maximum = 0
    for i in pos:
        maximum = max(len(i),maximum)
    for i in neg:
        maximum = max(len(i),maximum)
    k = maximum + 1
    while( k != 30):
        vpool = IDPool()
        cnf = CNF()
        for i in range(k):
            vpool.id(f"etat{i}")  # create k state form 0 to k-1
            vpool.id(f"etat{i}_is_final")  # create booleen to express if a state is final
            for j in range(k):
                for letter in alphabet:
                    vpool.id(f"etat{i}_to_etat{j}_with_{letter}")  # create a possible link with each state
        print("variable created")
        Basic_clauses(cnf, vpool, k, alphabet, pos, neg)
        minimal_node_clauses(cnf, vpool, k, alphabet)
        # Create a SAT solver
        print("basic litteral created")
        solver = Minisat22()
        # Add clauses to the solver
        for clause in cnf:
            solver.add_clause(clause)
        print("litteral added to solver")
        # Solve the SAT problem
        if solver.solve():
            model = solver.get_model()
            automate = create_automate(model, vpool, alphabet, k)
            show_automaton(automate)
            print("automate created")
            return automate
        else:
            k+=1
            print("restart")

# Q4
def complet_automate(cnf, vpool, k , alphabet):
    for i in range(k):
        for letter in alphabet:
            ORCLAUSE = []
            ORCLAUSE.append(-vpool.id(f"etat{i}"))
            for j in range(k):
                ORCLAUSE.append(vpool.id(f"etat{i}_to_etat{j}_with_{letter}"))
            cnf.append(ORCLAUSE)

def gen_autc(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    vpool = IDPool()
    cnf = CNF()
    for i in range(k):
        vpool.id(f"etat{i}")  # create k state form 0 to k-1
        vpool.id(f"etat{i}_is_final")  # create booleen to express if a state is final
        for j in range(k):
            for letter in alphabet:
                vpool.id(f"etat{i}_to_etat{j}_with_{letter}")  # create a possible link with each state
    print("variable created")
    Basic_clauses(cnf, vpool, k, alphabet, pos, neg)
    complet_automate(cnf, vpool, k, alphabet)
    # Create a SAT solver
    print("basic litteral created")
    solver = Minisat22()
    # Add clauses to the solver
    for clause in cnf:
        solver.add_clause(clause)
    print("litteral added to solver")
    # Solve the SAT problem
    if solver.solve():
        model = solver.get_model()
        automate = create_automate(model, vpool, alphabet, k)
        show_automaton(automate)
        print("automate created")
        return automate

# Q5
def reversible_clauses(cnf, vpool, k, alphabet):
    for i in range(k):
        for j in range(k):
            for letter in alphabet:
                for l in range(k):
                    if l!=i:
                        cnf.append([-vpool.id(f"etat{i}_to_etat{j}_with_{letter}"), -vpool.id(f"etat{l}_to_etat{j}_with_{letter}")])

def gen_autr(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    # À COMPLÉTER
    pass
    vpool = IDPool()
    cnf = CNF()
    for i in range(k):
        vpool.id(f"etat{i}")  # create k state form 0 to k-1
        vpool.id(f"etat{i}_is_final")  # create booleen to express if a state is final
        for j in range(k):
            for letter in alphabet:
                vpool.id(f"etat{i}_to_etat{j}_with_{letter}")  # create a possible link with each state
    print("variable created")
    Basic_clauses(cnf, vpool, k, alphabet, pos, neg)
    reversible_clauses(cnf, vpool, k, alphabet)
    # Create a SAT solver
    print("basic litteral created")
    solver = Minisat22()
    # Add clauses to the solver
    for clause in cnf:
        solver.add_clause(clause)
    print("litteral added to solver")
    # Solve the SAT problem
    if solver.solve():
        model = solver.get_model()
        automate = create_automate(model, vpool, alphabet, k)
        show_automaton(automate)
        print("automate created")
        return automate
# Q6
def gen_autcard(alphabet: str, pos: list[str], neg: list[str], k: int, ell: int) -> DFA:
    # À COMPLÉTER
    pass

# Q7
def gen_autn(alphabet: str, pos: list[str], neg: list[str], k: int) -> NFA:
    # À COMPLÉTER
    pass

def main():
    test_aut()
    test_minaut()
    test_autc()
    test_autr()
    test_autcard()
    test_autn()

if __name__ == '__main__':
    main()
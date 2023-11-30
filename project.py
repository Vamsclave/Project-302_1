from utils import *
from tests import *

from automata.fa.fa import FA
from automata.fa.dfa import DFA
from automata.fa.nfa import NFA

from pysat.solvers import Minisat22, Minicard
from pysat.formula import CNF, CNFPlus, IDPool
def P_clauses(cnf, vpool, k, P):
    for word in P:
        nodes_list = [([0],word)]
        finished_node = []
        while len(nodes_list) != 0:
            start_node = nodes_list.pop(0)
            if len(start_node[1]) != 0 :
                new_alpha = start_node[1][1:]
                for i in range(k):
                    nodes_list.append((start_node[0].append(i), new_alpha))
            else:
                finished_node.append(start_node[0])
        # all possibility for a word possibility OR possibility OR ... OR possibility
        ORClause = []
        for possibility in finished_node:
            # a possibility of a word t(q0,qi,a) AND t(qi,qj,b) AND .... AND F(qk)
            incnf = CNF()
            for i in range(len(word)):
                incnf.append(vpool.id(f"etat{possibility[i]}_to_etat{possibility[i+1]}_with_{word[i]}"))
            incnf.append(vpool.id(f"etat{possibility[len(word)]}_is_final"))
            ORClause.append(incnf)
        # adding clause for each word
        cnf.append(ORClause)
def N_clauses(cnf, vpool, k, N):
    for word in N:
        nodes_list = [([0],word)]
        finished_node = []
        while len(nodes_list) != 0:
            start_node = nodes_list.pop(0)
            if len(start_node[1]) != 0 :
                new_alpha = start_node[1][1:]
                for i in range(k):
                    nodes_list.append((start_node[0].append(i), new_alpha))
            else:
                finished_node.append(start_node[0])
        # not possibility AND  possibility  AND ... AND not possibility
        incnf = CNF()
        for possibility in finished_node:
            #  not t(q0,qi,a) OR not t(qi,qj,b) OR .... OR not F(qk)
            ORClause = []
            for i in range(len(word)):
                ORClause.append(-vpool.id(f"etat{possibility[i]}_to_etat{possibility[i+1]}_with_{word[i]}"))
            ORClause.append(-vpool.id(f"etat{possibility[len(word)]}_is_final"))
            incnf.append(ORClause)
        # adding clause for each word
        cnf.append(incnf)
def Basic_clauses(cnf, vpool, k, alphabet, P, N):
    cnf.append(vpool.id("etat0"))
    # F(qi) -> qi
    for i in range(1, k):
        cnf.append([-vpool.id(f"etat{i}_is_final"), vpool.id(f"etat{i}")])
    # t(qi,qj,a) -> (qi AND qj)
    for i in range(k):
        for j in range(k):
            # (AND all letter(-t(qi,qj,a) AND -t(qj,qi,a))) V (qi AND qj)
            ORCLAUSE = []
            # (qi and qj)
            qandq = CNF()
            qandq.append(vpool.id(f"etat{i}"))
            qandq.append(vpool.id(f"etat{j}"))
            ORCLAUSE.append(qandq)
            # AND all letter(-t(qi,qj,a) AND -t(qj,qi,a))
            incnf = CNF()
            for letter in alphabet:
                incnf.append(-vpool.id(f"etat{i}_to_etat{j}_with_{letter}"))
                incnf.append(-vpool.id(f"etat{j}_to_etat{i}_with_{letter}"))
            ORCLAUSE.append(incnf)
            cnf.append(ORCLAUSE)
    # t(qi,qj,a) -> (AND all k!=j -t(qi,qk,a))
    for i in range(k):
        for j in range(k):
            for letter in alphabet:
                # -t(qi,qj,a) V (AND all k!=j -t(qi,qk,a))
                ORCLAUSE = []
                # -t(qi,qj,a)
                ORCLAUSE.append(-vpool.id(f"etat{i}_to_etat{j}_with_{letter}"))
                # (AND all k!=j -t(qi,qk,a))
                outcnf = CNF()
                for l in range(k):
                    if l != j:
                        outcnf.append(-vpool.id(f"etat{i}_to_etat{l}_with_{letter}"))
                ORCLAUSE.append(outcnf)
    P_clauses(cnf, vpool, k, P)
    N_clauses(cnf, vpool, k, N)
# Q2



def gen_aut(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    vpool = IDPool()
    cnf = CNF()
    for i in range(k):
        vpool.id(f"etat{i}")# create k state form 0 to k-1
        vpool.id(f"etat{i}_is_final")# create booleen to express if a state is final
        for j in range(k):
            for letter in alphabet:
                vpool.id(f"etat{i}_to_etat{j}_with_{letter}")# create a possible link with each state
    Basic_clauses(cnf, vpool, k, alphabet, pos, neg)



# Q3
def gen_minaut(alphabet: str, pos: list[str], neg: list[str]) -> DFA:
    # À COMPLÉTER
    pass

# Q4
def gen_autc(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    # À COMPLÉTER
    pass

# Q5
def gen_autr(alphabet: str, pos: list[str], neg: list[str], k: int) -> DFA:
    # À COMPLÉTER
    pass

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

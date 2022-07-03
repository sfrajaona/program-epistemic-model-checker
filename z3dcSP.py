# from cvc5.pythonic import *
from z3 import *
import time

def allXor(p):
    if len(p) == 1:
        return p[0]
    else:
        return Xor(p[0], allXor(p[1:]))

if __name__ == '__main__':
    # for n in [100,200,400]: 
    for n in [10]: 
        P = BoolVector('p', n)
        C = BoolVector('c', n)
        x = Bool('x')
        nonobs0 = [P[i] for i in range(1,n)] + [C[i] for i in range(2,n)]
        e = allXor([allXor([P[i], C[i], C[(i+1) % n]]) for i in range(0, n)])
        phi = And([Implies(P[i], And([Not(P[j])  for j in range(0,n) if not (j==i)])) for i in range(0,n)])

        A = And([Not(P[i]) for i in range(1,n) ])
        tauB = And([Not(ForAll(nonobs0,Implies(And(phi,x==e),P[i]))) for i in range(1,n)])
        tauA = ForAll(nonobs0,Implies(And(phi,x==e),A))

        alpha1TauSP = Implies(Not(P[0]), Or(tauB, tauA))
        alpha1TauSPe = Implies(Not(P[0]), Or(tauB, And(A,tauA)))

        start_time = time.time()
        s = Solver()
        # s.add(And(phi, Not(alpha1Tau) ))
        s.add(And(And(phi,x==e), Not(alpha1TauSP) ))
        fout = open("z3dc.smt", "a")
        fout.write(s.sexpr())
        fout.close()
        print(s.check())
        print("n =", n) 
        print("--- %s seconds ---" % (time.time() - start_time))


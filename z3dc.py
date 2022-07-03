from z3 import *
import time

def allXor(p):
    if len(p) == 1:
        return p[0]
    else:
        return Xor(p[0], allXor(p[1:]))

if __name__ == '__main__':
    n = 3 # default number of cryptographers
    if (len(sys.argv)>3 or len(sys.argv)<2):
        print('arguments: (a1|a2|a3|g1) [<n>] the formula and <n> is no of cryptos >=3')
        exit()
    if (len(sys.argv)==3):
        try:
            n = int(sys.argv[2])
            if (n < 3):
                print('I was expecting a number >= 3')
                exit()
        except Exception:
            print('I was expecting a number, I cannot parse what you gave me')
            exit()

    formula = sys.argv[1]

    P = BoolVector('p', n)
    C = BoolVector('c', n)
    x = Bool('x')
    nonobs0 = [P[i] for i in range(1,n)] + [C[i] for i in range(2,n)]
    e = allXor([allXor([P[i], C[i], C[(i+1) % n]]) for i in range(0, n)])
    phi = And([Implies(P[i], And([Not(P[j])  for j in range(0,n) if not (j==i)])) for i in range(0,n)])

    alpha3Tau = (ForAll(x,
                 Implies(x==e,ForAll(nonobs0, Implies(And(phi,x==e),P[1])))))
    alpha2Tau = (ForAll(x,
                 Implies(x==e,
                 ForAll(nonobs0, 
                 Implies(And(phi,x==e),x==Or([P[i] for i in range(0,n) ]))))))
    gamma1Tau = (ForAll(nonobs0, 
                 Implies(phi, 
                 (ForAll(x,Implies(x==e,x==Or([P[i] for i in range(0,n) ])))))))

    # beta1 is more complicated
    A = And([Not(P[i]) for i in range(1,n) ])
    tauB = And([Not(ForAll(nonobs0,Implies(And(phi,x==e),P[i]))) for i in range(1,n)])
    tauKA = ForAll(nonobs0,Implies(x==e,A))
    alpha1Tau = ForAll(x,Implies(x==e, Implies(Not(P[0]),Or(tauB,tauKA))))

    start_time = time.time()
    s = Solver()
    s.add(And(phi, Not(alpha1Tau) ))
    print(s.check())
    print("n =", n) 
    print("--- %s seconds ---" % (time.time() - start_time))

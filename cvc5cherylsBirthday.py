from cvc5.pythonic import * 
import time

if __name__ == '__main__':
    try:
        f = open("cherylsBirthday.py",'w')
    except IOError:
        print("I could not find the file. Please generate it with ExampleCherylsBirthday.hs")

    uivar_bound = eval(f.readline())
    xivar_bound = eval(f.readline())

    month = Int('m') 
    day = Int('n') 
    UI = IntVector('u', uivar_bound+1)
    XI = IntVector('x', xivar_bound+1)

    phi = eval(f.readline())
    alpha = eval(f.readline())

    start_time = time.time()
    s = Solver()
    s.add(phi)
    s.add(alpha)
    print(s.check())
    print("--- %s seconds ---" % (time.time() - start_time))
    print(solve(And(alpha,phi)))

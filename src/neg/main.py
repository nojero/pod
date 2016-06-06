import z3
import itertools as it
import ptnet
#import example

def z3Int(x):
    assert(isinstance(x, ptnet.Transition) or isinstance(x,ptnet.Place))
    return z3.Int(repr(x))
    #return z3.Int(x.name)

def sub(e1=False,e2=False):
    fa = True
    for c1 in e1.pre:
        ex = False
        for c2 in e2.pre:
            ex = z3.Or(ex,z3Int(c1) == z3Int(c2))
        fa = z3.And(fa,ex)
    return fa

#Cota inferior para places/condiciones
BOUND_P = "bound_p"
#Cota superior para transitions/eventos
BOUND_T = "bound_t"
def SP_opt(on=False):
    domain = set()
    s = z3.Optimize()

    #Places
    for p in (on.places):
        domain.add(p)
        s.add(z3Int(p) > 0)
    for p1,p2 in it.combinations(on.places,2):
        s.add_soft(z3Int(p1) != z3Int(p2))

    #Transiciones
    for t1,t2 in it.combinations(on.trans,2):
        if(t1.label != t2.label):
            s.add(z3Int(t1) != z3Int(t2))
        s.add(z3.Implies(z3Int(t1) == z3Int(t2),z3.And(sub(t1,t2),sub(t2,t1))))
    for t in on.trans:
        domain.add(t)
        s.add(z3Int(t) <= z3.Int(BOUND_T))
        s.add(z3Int(t) > 0)
    s.minimize(z3.Int(BOUND_T))

    ret = s.check()
    if ret == z3.sat:
        ret = s.model()
        print ret
    else:
        ret = None
    return domain,ret

def SP(on=False):
    domain = set()
    s = z3.Solver()

    #Transiciones
    for t1,t2 in it.combinations(on.trans,2):
        #LAB
        if(t1.label != t2.label):
            s.add(z3Int(t1) != z3Int(t2))
        #PRE
        s.add(z3.Implies(z3Int(t1) == z3Int(t2),z3.And(sub(t1,t2),sub(t2,t1))))
    #creating domain
    for t in on.trans:
        domain.add(t)
        s.add(z3Int(t) > 0)
    for p in on.places:
        s.add(z3Int(p) > 0)
        domain.add(p)

    ret = s.check()
    if ret == z3.sat:
        ret = s.model()
        print ret
    else:
        ret = None
    return domain,ret


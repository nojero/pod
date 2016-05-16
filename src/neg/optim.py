import z3
import itertools as it
#import ptnet

#Nos aseguramos que sea una transicion
def z3Int(x):
    assert(isinstance(x, Transition))
    #return z3.Int(str(x))
    return z3.Int(x.name)

class On:
    def __init__(self):
        self.trans = []

class Transition:
    def __init__(self):
        self.label = ''
        self.name = ''

on1 = On()
ta = Transition()
ta.label = '1'
ta.name = 'e0'
tb = Transition()
tb.label = '4'
tb.name = 'e1'
tc = Transition()
tc.label = '1'
tc.name = 'e2'
td = Transition()
td.label = '2'
td.name = 'e3'
te = Transition()
te.label = '2'
te.name = 'e4'

on1.trans.append(ta)
on1.trans.append(tb)
on1.trans.append(tc)
on1.trans.append(td)
on1.trans.append(te)

def prueba(on=False):
    s = z3.Optimize()
    #unf.trans[0].label
    for t1,t2 in it.combinations(on.trans,2):
        if(t1.label != t2.label):
            s.add(z3Int(t1) != z3Int(t2))

    #optimizando
    for t in on.trans:
        s.add(z3Int(t) >= 0)
    s.minimize(z3Int(ta) + z3Int(tb) + z3Int(tc) + z3Int(td) + z3Int(te))
    #optimizando
    print s.check()
    print s.model()
    return

print prueba(on1)

#Negreada para probar BEGIN
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
#Negreada para probar END


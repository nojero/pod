#!/usr/bin/python

from net import *
from z3 import *
from time import time
from matrix import *
import pandas as pd

def z3Pair(x,y):
    assert(isinstance(x, Place) and isinstance(y, Place))
    return Int(str(repr(x)) + "-" + str(repr(y)))

def z3Int(x):
    assert(isinstance(x, Place))
    return Int(str(repr(x)))

def parseMatrix(name):
    """ Reads the *.excl file and saves the matrix as a dictionary. """
    ## The matrix contains STRINGS
    f = open(name)
    rank = len(f.readlines()[-1].decode())-1
    f.seek(0)
    d = {}
    for it, line in enumerate(f):
        d["p"+str(it)] = {}
        n = len(line)
        points = "."*(rank-n+1)
        newLine = line[:n-1] + points
        for it2, pt in enumerate(newLine):
            d["p"+str(it)]["p"+str(it2)] = pt
    f.close()
    return d

def getHalfspace(p, n):
    assert(isinstance(p, Place) and isinstance(n, Net))
    assert(p in n.places)
    halfspace = n.m0[p]
    for t in p.pre:
        halfspace += Int(repr(t))
    for t in p.post:
        halfspace -= Int(repr(t))
    return halfspace

def getMkEq(n):
    assert(isinstance(n, Net))
    mkEq = And(map(lambda p : getHalfspace(p,n) >= 0, n.places))
    return mkEq

def findUnits(inputfile, matrix, bound, op=False, timeout=100, verbose=False):
    assert(inputfile.endswith('.pnml'))
    assert(matrix.endswith('.excl'))
    n = Net()
    n.read(inputfile)
    if bound == None: bound = len(n.places)
    if op: s = Optimize(); s.minimize(Int("Bound"))
    else: s = Solver()#; s.add(Int("Bound") <= bound)
    s.set("timeout", timeout)
    excMatrix = parseMatrix(matrix)

    ### Prepares the encoding for exclusive places
    z3Trans =  map(lambda x: Int(repr(x)), n.trans)
    pre = And(map(lambda x : Int(repr(x)) >= 0, n.trans))
    pre = And(pre, getMkEq(n))

    ### This breaks the symmetry of the encoding based on the algorithm from
    ### "Exploiting symmetry in SMT problems" (CASE'11)
    if verbose: print "Starting encoding to break symmetry"
    iTime = time()
    T = set(map(lambda x : Int(str(repr(x))), n.places))
    ctsUnits = set(range(1, bound + 1))
    cts = set()
    while T != set() and len(cts) <= len(ctsUnits):
        t = T.pop()
        if ctsUnits.difference(cts) != set():
            c = ctsUnits.difference(cts).pop()
            cts.add(c)
        if cts != ctsUnits:
            s.add(Or(map(lambda x : t == x, cts)))
    eTime = time()
    if verbose: print "Done! (%s)" % (str(eTime - iTime))

    ### Places in the preset of a transition should belong to different units
    ### (unless the transition is dead, which we assume is not)
    if verbose: print "Starting encoding for preset and postset"
    iTime = time()
    for t in n.trans:
        for it, p1 in enumerate(list(t.pre)):
            for p2 in list(t.pre)[it+1:]:
                #para cada siuguiente, me aseguro de que esten
                #en unidades diferentes, porque los dos places pertenecen al preset de una transicion
                s.add(z3Pair(p1, p2) == 3)
                s.add(z3Int(p1) != z3Int(p2))
            for p2 in t.post:
                if op and len(t.pre) == 1 and len(t.post) == 1:
                    s.add_soft(z3Pair(p1, p2) == 0)
                elif op and len(t.pre) == 1 and len(t.post) > 1:
                    s.add_soft(z3Pair(p1, p2) == 1)
                elif op and len(t.pre) > 1 and len(t.post) == 1:
                    s.add_soft(z3Pair(p1, p2) == 1)
                elif op and len(t.pre) > 1 and len(t.post) > 1:
                    s.add_soft(z3Pair(p1, p2) == 0)
                else: continue
        for it, p1 in enumerate(list(t.post)):
            for p2 in list(t.post)[it+1:]:
                s.add(z3Pair(p1, p2) == 3)
                s.add(z3Int(p1) != z3Int(p2))
    eTime = time()
    if verbose: print "Done! (%s)" % (str(eTime - iTime))

    ### Places in the initial marking belong to different units
    if verbose: print "Starting encoding for initial marking"
    iTime = time()
    for it, p1 in enumerate(n.initialMk()):
        for p2 in n.initialMk()[it+1:]:
            #cada inicial en su propio grupo
            s.add(z3Pair(p1,p2) == 3)
    eTime = time()
    if verbose: print "Done! (%s)" % (str(eTime - iTime))

    if verbose: print "Starting encoding for marking equation and exclusive places"
    iTime = time()
    for it, p1 in enumerate(n.places):
        hs1 = getHalfspace(p1, n)
        mp1 = str(repr(p1))
        ### Domain of the variable to relate palces and units
        s.add(z3Int(p1) > 0)
        s.add(z3Int(p1) <= Int("Bound"))
        for p2 in n.places[it+1:]:
            hs2 = getHalfspace(p2, n)
            mp2 = str(repr(p2))
            ### Domain of the variable to relate units
            s.add(z3Pair(p1,p2) >= 0)
            s.add(z3Pair(p1,p2) <= 3)
            ### If two places belong to the same unit, they should be exclusive
            s.add(Implies(z3Pair(p1,p2) == 0, ForAll(z3Trans, (Implies(And(pre, hs1 > 0), hs2 == 0)))))
            ### We use the infromation given by the exclusive matrix
            if excMatrix[mp1][mp2] == "=":
                s.add(z3Pair(p1,p2) == 0)
                s.add(z3Int(p1) == Z3Int(p2))
            elif excMatrix[mp1][mp2] == "<":
                s.add(z3Pair(p1,p2) == 1)
                s.add(z3Int(p1) != Z3Int(p2))
            elif excMatrix[mp1][mp2] == ">":
                s.add(z3Pair(p1,p2) == 2)
                s.add(z3Int(p1) != Z3Int(p2))
            elif excMatrix[mp1][mp2] == ".":
                if op: s.add_soft(Or(z3Pair(p1,p2) == 0, z3Int(p1)p2 == 1, z3p1p2 == 2))
                else: pass
            elif excMatrix[mp1][mp2] == "0":
                s.add(z3Pair(p1,p2) == 3)
                s.add(z3Int(p1) != Z3Int(p2))
            elif excMatrix[mp1][mp2] == "1":
                if op: s.add_soft(Or(z3Pair(p1,p2) == 0, z3Int(p1)p2 == 1, z3p1p2 == 2))
                else: pass
            elif excMatrix[mp1][mp2] == "~":
                if op: s.add_soft(z3Pair(p1,p2) == 0)
                else: pass
            elif excMatrix[mp1][mp2] == "[":
                s.add(z3Pair(p1,p2) == 1)
                s.add(z3Int(p1) != Z3Int(p2))
            elif excMatrix[mp1][mp2] == "]":
                s.add(z3Pair(p1,p2) == 2)
                s.add(z3Int(p1) != Z3Int(p2))
            ### If the pair variable say the belong to the same unit, we impose so
            s.add(Implies(z3Pair(p1,p2) == 0, z3Int(p1) == Z3Int(p2)))
            ### If they are not related or related by hierarchy, they belong to different units
            s.add(Implies(z3Pair(p1,p2) != 0, z3Int(p1) != Z3Int(p2)))
    eTime = time()
    if verbose: print "Done! (%s)" % (str(eTime - iTime))

    if verbose: print "Launching the solver"
    iTime = time()
    lastModel = None
    s.add(Int("Bound") <= bound )
    sol = s.check()
    while sol == sat:
        lastModel = s.model()
        bound = lastModel[Int("Bound")]
        s.add(Int("Bound") < bound)
        sol = s.check()

    eTime = time()
    if verbose: print "Done! (%s)" % (str(eTime - iTime))

    for p in n.places:
        if lastModel != None:
            p.setUnit(int(str(lastModel[z3Int(p)])))

    units = ""
    for u in range(1, int(str(bound)) + 1):
        placesForUnit = filter(lambda p : p.unit == u, n.places)
        placesForUnit = map(lambda p : str(p.name), placesForUnit)
        placesForUnit.append("-1")
        unit = " ".join(placesForUnit)
        units += "%s\n" % (unit)

    return units

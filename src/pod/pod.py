"""
pod [OPTIONS] COMMAND LOGFILE/PNMLFILE [INDEPFILE]

Bla bla bla

COMMAND is one of Bla
LOGFILE is the path to an XML file containing formulas (MCC 2015 format)

And OPTIONS is zero or more of the following options

 --log-first=N
   Use only the first N sequences of the log file.

 ...

pod [OPTIONS] extract-dependence    PNML
pod [OPTIONS] dump-log              LOGFILE
pod [OPTIONS] dump-pes              LOGFILE INDEPFILE
pod [OPTIONS] dump-bp               LOGFILE INDEPFILE
pod [OPTIONS] dump-encoding     LOGFILE INDEPFILE
pod [OPTIONS] dump-merge            LOGFILE INDEPFILE
pod [OPTIONS] merge                 LOGFILE INDEPFILE


OPTIONS:

--help, -h
--log-first=n
--log-only=1,2,4
--log-exclude=7,23
--output=PATH

"""

try :
    import os
    import sys
    import resource
    import networkx
    import argparse

    from util import *
    from log import *
    from merging import *

    import z3
    import ptnet
    import pes
except ImportError, e:
    util.error_missing_package (e)

if sys.version_info < (2, 7, 0) or sys.version_info >= (3, 0, 0) :
    print ("")
    print ("*** ERROR ***")
    print ("This tool relies on Python 2.7!!")
    print ("Install Python 2.7 or modify the first line of the file 'po-discovery.py' so that it calls Python 2.7")
    print ("")
    sys.exit (1)

class Pod :
    def __init__ (self) :
        self.log_path = ""
        self.log_first = 0
        self.log_only = []
        self.log_exclude = []
        self.log = None

        self.output_path = ""
        self.indep_path = ""
        self.command = ""

    def parse_cmdline_args (self) :

        cmd_choices = ["extract-dependence", "dump-log", "dump-pes",
                "dump-bp", "dump-encoding", "dump-merge", "merge"]
        #p = argparse.ArgumentParser (usage = __doc__, add_help=False)
        p = argparse.ArgumentParser (usage=__doc__)
        #p.add_argument ("-h", "--help", action="store_true")
        p.add_argument ("--log-first", type=int)
        p.add_argument ("--log-only")
        p.add_argument ("--log-exclude", default=[])
        p.add_argument ("--output")
        #p.add_argument ("--format", choices=["pdf","dot","pnml"])

        p.add_argument ('cmd', metavar="COMMAND", choices=cmd_choices)
        p.add_argument ('log_pnml', metavar="LOGFILE/PNML")
        p.add_argument ('indep', metavar="INDEPFILE", nargs="?", default=None)

        args = p.parse_args ()
        print "pod: args:", args

        #if args.help :
        #    print __doc__
        #    sys.exit (0);

        self.command = args.cmd
        self.indep_path = args.indep
        self.log_path = args.log_pnml
        self.log_exclude = args.log_exclude
        self.log_only = args.log_only
        self.log_first = args.log_first

        if args.output != None :
            self.output_path = args.output
        else :
            d = {
                "extract-dependence" : "dependence.txt",
                "dump-pes"           : "pes.pdf",
                "dump-bp"            : "bp.pdf",
                "dump-encoding"      : "encoding.smt2",
                "merge"              : "output.pnml"}
            self.output_path = d.get (self.command, "output.txt")
        for opt in ["log_path", "log_first", "log_only", "log_exclude",
                    "output_path", "indep_path", "command"] :
            output_pair (sys.stdout, opt, self.__dict__[opt], 11, "pod: args: ")

    def main (self) :
        self.parse_cmdline_args ()

        if self.command == "extract-dependence" :
            self.cmd_extract_dependence ()
        elif self.command == "dump-log" :
            self.cmd_dump_log ()
        else :
            raise Exception, "Shit happened!"

    def cmd_extract_dependence (self) :

        # load the net
        net = load_net (self.log_path, "pnml", "pod: extract: ")

        # create a dependence relation and fill it from the net
        dep = Depen ()
        print "pod: extract: extracting dependence relation ..."
        dep.from_net (net)

        # XXX - hack: ensure that the relation is "positively" stored
        assert (dep.negate == False)
        print "pod: extract: done, %d pairs" % len (dep.pairs)

        # warnings
        s = set ()
        for t in net.trans :
            if " " in t.name :
                print "pod: extract: WARNING: transition '%s' contains spaces in the name" % t.name
            if t.name in s :
                print "pod: extract: WARNING: 2 transition with same name '%s'" % t.name
            s.add (t.name)

        # save
        f = open (self.output_path, "w")
        f.write ("# Dependence relation automatically extracted from:\n")
        f.write ("# %s\n" % self.log_path)
        for (t1, t2) in dep.pairs :
            f.write ("%s %s\n" % (t1.name, t2.name))
        f.close ()
        print "pod: extract: output saved to '%s'" % self.output_path

    def __assert_merge_pre (self, unf, me) :

        # has a bottom event
        # it is the unflding in the me
        assert (len (unf.events[0].pre) == 0)
        assert (unf == me.enc.unf)

        # inverse labelling is good
        m = unf.new_mark ()
        for a in unf.net.trans :
            assert (len (a.inverse_label) >= 1)
            for e in a.inverse_label :
                assert (e.m != m)
                e.m = m
        for e in unf.events :
            assert (e.m == m)

    def __assert_merge_post (self, unf, me, e2t, c2p) :

        assert (len (e2t) == len (unf.events))
        assert (len (c2p) == len (unf.conds))

        for e,t in e2t.items () :
            for ee in e2t :
                if e2t[ee] == t :
                    assert (me.are_merged (e, ee))
                    self.__assert_merge_subset (me, e, ee)
                    self.__assert_merge_subset (me, ee, e)
        for c,p in c2p.items () :
            for cc in c2p :
                if c2p[cc] == p :
                    assert (me.are_merged (c, cc))
    
    def __assert_merge_subset (self, me, e, ee) :
        # all events in preset and postset of e are merged with at least
        # one of ee
        for x,y in [(e.pre, ee.pre), (e.post, ee.post)] :
            for c in x :
                assert (reduce (lambda a, b : a or b, \
                        map (lambda cc : me.are_merged (c, cc), y)))

    def merge (self, unf, me) :
        self.__assert_merge_pre (unf, me)
        net = ptnet.Net (True)

        # merge events
        e2t = {}
        c2p = {}
        for a in unf.net.trans :
            d = {}
            for e in a.inverse_label :
                found = False
                for ee in d :
                    if me.are_merged (e, ee) :
                        d[ee].add (e)
                        found = True
                        break
                if not found :
                    d[e] = set ([e])
            print "podisc: merging: label", repr (a), "result:", d.values ()
            for e,evs in d.items () :
                t = net.trans_add (repr ((a, evs)))
                for ee in evs : e2t[ee] = t

        # merge transitions
        d = {}
        for c in unf.conds :
            found = False
            for cc in d :
                if me.are_merged (c, cc) :
                    d[cc].add (c)
                    found = True
                    break
            if not found :
                d[c] = set ([c])
        print "podisc: merging: conditions:", d.values ()
        for c,conds in d.items () :
            p = net.place_add (repr (conds))
            for c in conds : c2p[c] = p

        self.__assert_merge_post (unf, me, e2t, c2p)

        # build flow
        for e in e2t :
            for c in e.pre :
                e2t[e].pre_add (c2p[c])
            for c in e.post :
                e2t[e].post_add (c2p[c])

        # build initial marking
        for c in unf.events[0].post :
            net.m0[c2p[c]] = 1

        return net

    def pes_to_bp (self, es, indep) :
        unf = ptnet.Unfolding ()

        # generate the events of the unfolding
        ev_tab = self.__pes_to_bp_gen_events (es, unf)
        print 'ev_tab', ev_tab

        # search for the cliques in the conflict relation and make a table
        cfl_tab = self.__pes_to_bp_build_conflict_table (es)
        cfl_tab = self.__pes_to_bp_conflict_table_pick_single (es, cfl_tab)
        print 'cfl_tab', cfl_tab

        # generate one condition and related causalities for every clique 
        pre_tab = self.__pes_to_bp_gen_conds_cfl (es, unf, cfl_tab, ev_tab)

        # for every two events in causal relation in the PES, generate
        # conditions (skiping causalities already introduced before)
        pre_tab = self.__pes_to_bp_gen_conds_pre_clique_based (es, unf, ev_tab, pre_tab, indep)
        #pre_tab = self.__pes_to_bp_gen_conds_pre (es, unf, ev_tab, pre_tab)

        # we are done!
        return unf

    def __pes_to_bp_gen_events (self, es, unf) :
        ev_tab = {}
        action_set = set ()
        for e in es.events :
            action_set.add (e.label)
            unfe = unf.event_add (e.label)
            ev_tab[e] = unfe

        # XXX - this is somehow a hack, but it will hopefully work
        unf.net.trans = list (action_set)
        return ev_tab

    def __pes_to_bp_build_conflict_table (self, es) :
        # - create an undirected graph representing the conflicts
        # - find all maximal cliques
        # - for each one of them, find the list of maximal events in
        #   intersection of local configurations of the events in the clique
        # - build the table

        g = networkx.Graph ()
        tab = {}
        for e in es.events :
            for ep in e.cfl :
                g.add_edge (e, ep)
        for clique in networkx.find_cliques (g) :
            local_configs = [es.get_local_config (e) for e in clique]
            c = reduce (lambda c1, c2 : c1.intersect_with (c2), local_configs)
            tup = (tuple (c.maximal ()), tuple (clique))
            for e in clique :
                tab[e] = tup
        return tab

    def __pes_to_bp_conflict_table_pick_single (self, es, cfl_tab) :
        tab = {}
        for (maxevs, clique) in cfl_tab.values () :
            e = maxevs[0] if len (maxevs) else None
            tup = (e, clique)
            for e in clique :
                tab[e] = tup
        return tab

    def __pes_to_bp_gen_conds_cfl (self, es, unf, cfl_tab, ev_tab) :
        pre_tab = {}
        for (epre, clique) in set (cfl_tab.values ()) :
            pre = [ev_tab[epre]] if epre != None else []
            post = [ev_tab[e] for e in clique]
            c = unf.cond_add (None, pre, post)
            for e in clique :
                pre_tab[epre, e] = c
        return pre_tab

    def __pes_to_bp_gen_conds_pre (self, es, unf, ev_tab, pre_tab) :
        for e in es.events :
            for ep in e.pre :
                if (ep, e) not in pre_tab :
                    c = unf.cond_add (None, [ev_tab[ep]], [ev_tab[e]])
                    pre_tab[ep, e] = c
            if len (e.pre) == 0 :
                if (None, e) not in pre_tab :
                    c = unf.cond_add (None, [], [ev_tab[e]])
                    pre_tab[None, e] = c
        return pre_tab

    def __pes_to_bp_gen_conds_pre_clique_based (self, es, unf, ev_tab, pre_tab, indep) :
        for e in es.events :
            # for all events in e.post, build graph whose edges are
            # the dependence relation
            g = networkx.Graph ()
            g.add_nodes_from (e.post)
            for e1 in e.post :
                for e2 in e.post :
                    if e1 != e2 and not indep[e1.label, e2.label] :
                        g.add_edge (e1, e2)
            # for every clique, generate one condition
            for clique in networkx.find_cliques (g) :
                # remove events for which there is already condition
                for ep in [ep for ep in clique if (e, ep) in pre_tab] :
                    clique.remove (ep)
                if len (clique) == 0 : continue
                unfpostevs = [ev_tab[ep] for ep in clique]
                c = unf.cond_add (None, [ev_tab[e]], unfpostevs)
                for ep in clique :
                    pre_tab[e, ep] = c
            # events with empty preset will never occurr in previous
            # search, deal with them separately
            if len (e.pre) == 0 :
                if (None, e) not in pre_tab :
                    c = unf.cond_add (None, [], [ev_tab[e]])
                    pre_tab[None, e] = c
        return pre_tab

def main () :
    # parse arguments (import argparse)
    # assert that input net is 1-safe!!

    # TODO
    # x support for reading the model
    # x and building a Merge_equivalence
    # - support for merging the unfolding given a Merge_equivalence
    # - debug on some small example, start with gas_station.cuf, depth=2,3,4

    pass

# vi:ts=4:sw=4:et:

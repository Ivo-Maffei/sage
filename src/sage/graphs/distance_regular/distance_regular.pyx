# cython: profile=False
# -*- coding: utf-8 -*-
r"""
This module aims at constructing distance-regular graphs.

This module provide the construction of several distance-regular graphs.
In addition we implemented multiple utility functions for such graphs.


EXAMPLES::

<Lots and lots of examples>

AUTHORS:

- Ivo Maffei (2005-01-03): initial version

"""

# ****************************************************************************
#       Copyright (C) 2013 Ivo Maffei <ivomaffei@gmail.com>
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 2 of the License, or
# (at your option) any later version.
#                  https://www.gnu.org/licenses/
# ****************************************************************************

# project C import
from cysignals.signals cimport sig_check

# sage imports
from sage.graphs.graph_generators import GraphGenerators
from sage.graphs.graph import Graph
from sage.arith.misc import is_prime_power, is_prime
from sage.combinat.q_analogues import q_binomial
from sage.combinat.integer_vector import IntegerVectors
from sage.matrix.matrix_space import MatrixSpace
from sage.rings.rational cimport Rational
from sage.rings.integer cimport Integer
from sage.combinat.designs import design_catalog as Sage_Designs
from sage.graphs.strongly_regular_db import strongly_regular_graph
from sage.combinat.subset import Subsets
from sage.sets.set import Set

#import other distance regular files (to be change later
from distance_regular.codegraphs import *
from distance_regular.sporadic import *
from distance_regular.unbounded_diameter import *
from distance_regular.unbounded_order import *
#from distance_regular.utils import *


################################################################################
# UTILITY FUNCTIONS
def _add_vectors(v, w):
    cdef int n = len(v)
    
    result = []
    for i in range(n):
        result.append( v[i] + w[i] )
        
    return tuple(result)

    
def group_2F4(const int q):
    #we must have q = 2^{2m +1}
    #and we need m
    i = 2

    m = 0
    while i < q:
        i = i*4
        m = m +1

    if i != q:
        raise ValueError("invalid q")

    if m == 0:
        raise ValueError("use AtlasRep")

    #get some constants
    libgap.eval("q := "+str(q)+";")
    libgap.eval("F := GF(q);")
    libgap.eval("s := 2^"+str(m)+";")
    libgap.eval("o := One(F);")
    libgap.eval("ep := PrimitiveRoot(F);")

    #matrix x
    libgap.eval("x := NullMat(26,26,F);")
    libgap.eval("x[2,3]:=o;")
    libgap.eval("x[2,4]:=o;")
    libgap.eval("x[2,6]:=o;")
    libgap.eval("x[3,4]:=o;")
    libgap.eval("x[4,6]:=o;")
    libgap.eval("x[5,7]:=o;")
    libgap.eval("x[5,9]:=o;")
    libgap.eval("x[5,11]:=o;")
    libgap.eval("x[7,9]:=o;")
    libgap.eval("x[9,11]:=o;")
    libgap.eval("x[10,12]:=o;")
    libgap.eval("x[10,16]:=o;")
    libgap.eval("x[10,18]:=o;")
    libgap.eval("x[12,13]:=o;")
    libgap.eval("x[12,16]:=o;")
    libgap.eval("x[14,16]:=o;")
    libgap.eval("x[14,18]:=o;")
    libgap.eval("x[15,17]:=o;")
    libgap.eval("x[15,19]:=o;")
    libgap.eval("x[15,22]:=o;")
    libgap.eval("x[16,18]:=o;")
    libgap.eval("x[17,19]:=o;")
    libgap.eval("x[19,22]:=o;")
    libgap.eval("x[21,23]:=o;")
    libgap.eval("x[21,24]:=o;")
    libgap.eval("x[21,25]:=o;")
    libgap.eval("x[23,24]:=o;")
    libgap.eval("x[24,25]:=o;")

    #matrix n
    libgap.eval("n := NullMat(26,26,F);")
    libgap.eval("n[1,2]:=o;")
    libgap.eval("n[2,10]:=o;")
    libgap.eval("n[3,5]:=o;")
    libgap.eval("n[4,3]:=o;")
    libgap.eval("n[5,16]:=o;")
    libgap.eval("n[6,1]:=o;")
    libgap.eval("n[7,12]:=o;")
    libgap.eval("n[8,7]:=o;")
    libgap.eval("n[9,8]:=o;")
    libgap.eval("n[10,21]:=o;")
    libgap.eval("n[11,4]:=o;")
    libgap.eval("n[12,17]:=o;")
    libgap.eval("n[13,13]:=o;")
    libgap.eval("n[13,14]:=o;")
    libgap.eval("n[14,14]:=o;")
    libgap.eval("n[15,23]:=o;")
    libgap.eval("n[16,9]:=o;")
    libgap.eval("n[17,20]:=o;")
    libgap.eval("n[18,6]:=o;")
    libgap.eval("n[19,16]:=o;")
    libgap.eval("n[20,19]:=o;")
    libgap.eval("n[21,26]:=o;")
    libgap.eval("n[22,11]:=o;")
    libgap.eval("n[23,24]:=o;")
    libgap.eval("n[24,22]:=o;")
    libgap.eval("n[25,18]:=o;")
    libgap.eval("n[26,25]:=o;")


    #matrix m2
    libgap.eval("m2 := x*n;")

    #matrix h
    libgap.eval("h := NullMat(26,26,F);")

    for i in range(1,27):
        pos = "h["+str(i)+","+str(i)+"] :="
        if i in {2,5,15,21}:
            libgap.eval(pos+"ep;") 
        elif i in {6,11,22,25}:
            libgap.eval(pos+"ep^(-1);")
        elif i in {4,9,19,24}:
            libgap.eval(pos+"ep^(-s+1);")
        elif i in {3,7,17,23}:
            libgap.eval(pos+"ep^(s-1);")
        elif i == 10:
            libgap.eval(pos+"ep^s;")
        elif i == 12:
            libgap.eval(pos+"ep^(-s+2);")
        elif i == 16:
            libgap.eval(pos+"ep^(s-2);")
        elif i == 18:
            libgap.eval(pos+"ep^(-s);")
        else:
            libgap.eval(pos+"o;")
    #done h

    #now h and m2 are generators of the group

    libgap.eval("x := GroupByGenerators([m2,h]);")
    libgap.eval('SetName(x,Concatenation("2F4(",String(q),")"));')
    #size comes from bcn book
    libgap.eval("SetSize(x,q^24*(q^2-1)*(q^6+1)*(q^8-1)*(q^12+1));")
    return libgap.eval("x")
    
# START GRAPH RELATED FUNCTIONS

# given a graph G it halves the graph
def halve_graph(G) :
    r"""
    Return a half of this graph.

    Given a graph $G$ which is assumed to be bipartite,
    this function returns a graph $H$ which is half of $G$.
    That is, $H$ is a subgraph of $G$ consisting of all vertices in one
    of the 2 distinct partitions of G where $x,y \in H$ are
    adjecent if and only if $d(x,y) = 2$ in $G$.

    INPUT:

    - ``G`` : a bipartite graph

    EXAMPLES:

        tbd

    ..NOTE::
    
        This function will raise a ``ValueError``
        if the input graph is not bipartite.

    TESTS::
    """
    
    if not G.is_bipartite():
        raise ValueError(
            "The input graph is not bipartite")
    
    H = GraphGenerators.EmptyGraph()
    queue = [G.vertices()[0]] # queue of vertex to follow
    H.add_vertex(G.vertices()[0])
    while queue:
        v = queue.pop(0)
        close = G.neighbors(v)
        candidate = [ x for c in close for x in G.neighbors(c) ]# flatten map G.neighbors(_) close
        for w in candidate:
            if G.distance(v,w) == 2:
                if w not in H:
                     queue.append(w)
                     H.add_vertex(w)
                H.add_edge(v,w)

    H.name("Halved %s" % G.name() )
    
    return H

def fold_graph( G ):
    r"""
    Assume G is antipodal and computes its folded graph:

    G antipodal means G_d is a disjoint union of cliques
    (G_d is the distance graph of G and d is its diameter)

    the fold graph (V_f,E_f) is:
    V_f = maximal cliques of G_d
    E_f = { (c_1,c_2) | \exists u \in c_1, v \in c_2 s.t. (u,v) \in E }
    """

    def has_edge( c1, c2 ):
        for u in c1:
            for v in c2:
                if G.has_edge(u,v) : return True

        return False

    #here we should check that G is antipodal

    G_d = G.distance_graph(G.diameter())

    # to create the vertex set:
    # make a list of sets; each set a singleto containing a vertex of G
    # iterate through the list
    # for each singleton set, add to that sets all neighbours of its element in G_d
    # (like a disjoint set forest)
    # since G_d is a union of disjoint cliques all nodes in a set are a maximal clique
    # atm we have a sillier implementation
    cdef list cliques = []
    cdef list vertices = G.vertices()
    for v in vertices:
        clique = frozenset(G_d.neighbors(v, closed=True))
        cliques.append(clique)

    cdef int n = len(cliques)
    cdef list edges = []
    for i in range(n):
        c1 = cliques[i]
        for j in range(i+1, n):
            c2 = cliques[j]
            #is there an edge (c1,c2)
            if has_edge(c1,c2): edges.append( (c1,c2) )

    F = Graph(edges, format='list_of_edges')
    F.name("Fold of %s" % (G.name()) )
    return F

def bipartite_double_graph(G):
    r"""
    This function return the biparite doubled graph of G
    the vertices of double graph are 2 copies of V
    the edges are (u_1,v_2), (u_2,v_1) for any (u,v) in E
    """
    #in order to have to copies of each vertex we do
    #(0,v) and (1,v)

    cdef list edges = []
    for (u,v,l) in G.edges():
        u1 = (0,u)
        u2 = (1,u)
        v1 = (0,v)
        v2 = (1,v)
        
        edges.append((u1,v2))
        edges.append((u2,v1))

    H = Graph(edges, format='list_of_edges')
    H.name("Bipartite Double of %s"%(G.name()))

    return H

def extended_biparitite_double_graph(G):
    r"""
    Same as bipartite double but we add edges (u_1,u_2) for u \in V
    """
    H = bipartite_double_graph(G)
    for u in G.vertices():
        u1 = (0,u)
        u2 = (1,u)

        H.add_edge((u1,u2))

    H.name("Extended %s"%(H.name()))
    return H

################################################################################
# BIG FUNCTIONS THAT GROUP CONSTRUCTIONS

def distance_regular_graph_with_classical_parameters( const int d,
                                                      const int b,
                                                      input_alpha,
                                                      input_beta ):
    r"""
    Return a distance-regular graph $G$ with the given classical parameters.

    We assume $d \geq 3$.
    If no distance-regular graph satisfying the input parameters is found,
    then this function will raise a ValueError

    INPUT:

    - ``d`` -- integer; we assume this is greater or equal than 3
    - ``b`` -- integer
    - ``alpha, beta`` -- numbers

    OUTPUT:
    
    A distance-regular graph $G$ with classical parameters ``(d,b,alpha,beta)``

    EXAMPLES::
    
        sage: g = distance_regulat_graph_with_classical_parameters(3,-2,-4,10)
        sage: g.is_distance_regular()
        True
        sage: a = intersection_array_from_graph(g)
        sage: get_classical_parameters_from_intersection_array(a)
        (3,-2,-4,10)0
    
    .. NOTE::
    
        The outputted graph is NOT unique. There might be another graph with
        the given classical parameters. However this function is deterministic,
        i.e. it will always output the same graph given the same input.

    TESTS::

        tbd

    """
    
    def is_power_of( const int num, const int base ):
        # this functions checks if num = base^k for some k in N and return k
        # if no such k exists, then -1 is returned
        cdef int baseToK = base
        cdef int k = 1
        #invariant : baseToK = base^k
        while ( baseToK < num ):
            baseToK *= base
            k += 1

        if baseToK == num:
            return k
        else:
            return -1
    # end is_power_of

    def q_of(const int num, const int exp ):
        # return prime power q s.t. num = q^exp
        # otherwise return -1
        (b,k) = is_prime_power(num, True)
        # if k != 0, then b^k = num
        # if k == 0, then num is not a prime power
        if k != 0 and (k % exp) == 0:
            # q^exp = b^k => q = b^i where i = k / exp
            return  b**(k/exp)
        else:
            return -1
    # end q_of

    if d < 3:
        raise ValueError(
            "We only consider distance-regular graphs with diameter >=3")
    
    alpha = Rational(input_alpha)
    beta = Rational(input_beta)
    
    if b == 1 :
        if alpha == 1 and beta >= d:#since beta+d = n >= 2*d
            # Johnson Graph
            return GraphGenerators.JohnsonGraph(beta+d, d)
        elif d == 3 and alpha == 4 and beta == 9:
            # Gosset graph
            return GraphGenerators.GossetGraph()
        elif alpha == 0:
            # Hamming Graph
            n = beta + 1
            return GraphGenerators.HammingGraph(d,n)
        elif alpha == 2 and ( beta == 2*d + 1 or beta == 2*d - 1):
            # Halved cube graph
            if beta == 2*d +1: # then n = beta
                return halved_cube(beta)
            else: # then n = beta + 1
                return halved_cube(beta+1)
        else :
            raise ValueError(
                "No distance-regular graph with the given parameters exists")
            
    elif b == -2:
        if d == 3 and alpha == -4 and beta == 10:
            # large Witt graph
            return large_Witt_graph()
        elif d == 3 and alpha == -2 and beta == 5:
            # truncate Witt graph
           return truncated_Witt_graph()
        elif d == 3 and alpha == -3 and beta == 8:
            #goolay code graph
            return extended_ternary_Golay_code_graph()
        pass
    
    elif b < 0 and is_prime_power(b):
        if alpha +1 == (1 + b*b)/(1 + b) and beta +1 == q_binomial(d+1,1,b):
            # U(2d,r)
            return GraphGenerators.UnitaryDualPolarGraph(2*d,-b)
        elif d == 3 and alpha + 1 == 1 / (1+b) and beta + 1 == q_binomial(3,1,-b):
            q = -b
            if q < 4:
                return graph_3D42(q)
            else:
                raise ValueError("too big")
            pass
        elif alpha + 1 == b and beta + 1 == b**d:
            q = (-b)**2 # b = -r
            return hermitean_form_graph(d,q)
        pass
    
    elif is_prime_power(b):
        if alpha == b and is_power_of( (beta +1)*(b-1)+1, b ) >= d+1:
            # we checked that beta + 1 = (b^(n-d+1) - 1)/(b - 1) for n >= 2d
            # Grassmann graph
            pass
        elif alpha == 0 and is_power_of( beta, b ) in {0, 0.5, 1, 1.5, 2}:
            # dual polar graphs
            e = is_power_of( beta, b )
            if e == 0:
                #maximal Witt index
                pass
            if e == 1:
                #dual sympletic
                print("sympletic dual polar %d,%d"%(2*d,b))
                return GraphGenerators.SymplecticDualPolarGraph(2*d, b)
            elif e == 2:
                #non maximal Witt index
                pass
            elif e == 1.5:
                #hermitean form
                r = q_of(b,2)#b=r^2
                if r == -1:
                    raise ValueError("something wrong")
                return GraphGenerators.UnitaryDualPolarGraph(2*d+1,r)
            elif e == 0.5:
                #other hermitean form
                r = q_of(b,2)#b=r^2
                if r == -1:
                    raise ValueError("something wrong")
                
                return GraphGenerators.UnitaryDualPolarGraph(2*d,r)
                
        elif ( q_of(b,2) != -1 and alpha + 1 == q_binomial(3, 1, q_of(b,2))
               and beta + 1 in { q_binomial(2*d+2, 1, q_of(b,2)),
                                 q_binomial(2*d, 1, q_of(b,2)) }
        ):
            # half dual polar graph or dist. 1 or 2 in sympletic dual polar graphs
            pass
        elif ( d == 3 and q_of(b,4) != -1
               and alpha + 1 == q_binomial(5, 1, q_of(b,4))
               and beta + 1 == q_binomial( 10, 1, q_of(b,4))
        ):
            raise ValueError(
                "Exceptional Lie graph E_{7,7}(%d). Too big to be constructed"%(q_of(b,4)) )
        elif alpha + 1 == b and is_power_of( beta+1, b) >= d:
            # bilinear form
            e = is_power_of(beta+1, b)
            return bilinear_form_graph(d,e,b)
        elif ( q_of(b,2) != -1 and alpha + 1 == b
               and beta + 1 in { q_of(b,2)**(2*d-1), q_of(b,2)**(2*d+1) }
        ):
            # alternating form graphs or quadratic forms
            q = q_of(b,2)
            if beta + 1 == q**(2*d-1):
                n = 2*d
            else:
                n = 2*d+1
            return alternating_form_graph(n,q)
        elif ( d == 3 and q_of(b,4) != -1 and alpha + 1 == b
               and beta + 1 == q_of(b,4)**9
        ):
            raise ValueError(
                "Affine E_6(%d) graph. Too big to be constructed"%(q_of(b,4)) )
        pass

    raise ValueError(
        "Can't find a distance-regular graph with the given parameters")
        
    
def pseudo_partition_graph(m,a):
    r""" p 198"""
    if a == 0:
        return fold_graph(GraphGenerators.HammingGraph(m,2))
    elif a == 1:
        return fold_graph(GraphGenerators.JohnsonGraph(2*m,m))
    elif a == 2:
        return fold_graph(halved_cube(2*m))

    if m >= 8:
        raise ValueError("no graph with m >=8 and a \notin {0,1,2} exists")

    raise ValueError("no known graph exists")

def dist_reg_near_polygon(list arr):
    r"""
    Returns a dist reg graph which is a near polygon with the given intersection array

    I NEED TO BE CAREFUL WITH ERRORS: invalid array or unknown graph????
    """

    d = len(arr)
    l = is_near_polygon(arr)
    if l == -1 or d %2 == 1:
        raise ValueError("no near polygon exists with such int array")

    d = d // 2
    k = arr[0]

    if k == (l+1)*arr[2*d-1]:
        n = 2*d
        g = 2
    else:
        n = 2*d +1
        g = 1

    if k == 2 and l == 0:
        #polygon, but still check c_i's
        for i in range(1,d):
            if arr[d-1+i] != 1:
                raise ValueError("invalide int. array")
        if arr[2*d-1] != g:
            raise ValueError("invalid int arr")
        
        return polygon(n)

    elif l == 0 and k == d+1 and n == 2*d +1:
        #odd graph
        #still check c_i's
        for i in range(1,d+1):
            #c_{2j} = j
            #c_{2j -1} = j
            #so c_i = (i+1) // 2
            if arr[d-1+i] != (i+1) // 2:
                raise ValueError("invalid int arr")

        #what I call Odd(n) is Odd(n+1) in Sage
        return GraphGenerators.OddGraph(d+1)
    elif l == 0 and n == 2*d:
        #R3 (double grassman or odd)
        if d % 2 == 0:
            raise ValueError("invalid int arr")
        e = (d-1) // 2
        if k == e+1:
            #double odd
            #c_i need to satisfies the same as above
            for i in range(1,d+1):
                if arr[d-1+i] != (i+1) // 2:
                    raise ValueError("invalid int arr")
                
            #I postulate that doubled_odd_graph(x) has diameter 2*x +1
            #I should prove it
            return doubled_odd_graph(e)
        else:
            #we have double grassman
            #k = q_binomial(e+1,1,q) for some prime power q
            #c_j = q_binomail( (j+1)//2, 1, q)
            #so c_3 = q_binomial( 2,1,q) = q+1
            #we need d >= 3
            q = arr[d-1+3] -1
            if not is_prime_power(q) or k != q_binomial(e+1,1,q):
                raise ValueError("invalid int arr")

            #now check c_i's
            for i in range(1,d+1):
                if arr[d-1+i] != q_binomial( (i+1)//2, 1,q):
                    raise ValueError("invalid int arr")
            #note that the diameter of the double grassman graph (q',n',e')
            #is n'
            return double_Grassman(q,d,e)
        
    # classical parameters or pseudo partition
    # we assume that those are already ruled out
    raise ValueError("unknown graph")        


def graph_with_intersection_array( list arr ):
    def is_generalised_2d_gon(a):
        d = len(a)/2
        #c_1,...,c_{d-1} = 1
        for i in range(1,d):
            if a[d+i-1] != 1: return (-1,-1)

        t = a[2*d-1] -1 #c_d-1
        
        # b_0 = s(t+1)
        if a[0] % (t+1) != 0: return (-1,-1)
        s = a[0] / (t+1)
        
        #lamda = s - 1 = b_0 - b_1 - c_1
        if s -1 != a[0] - a[1] - a[d]: return (-1,-1)

        #b_i = st
        for i in range(1,d):
            if a[i] != s*t: return (-1,-1)

        #otherwise we have it
        return (s,t)
        
    n = len(arr)
    if n % 2 != 0:
        raise ValueError("array is not a valid intersection array")
    d = n / 2

    if d > 8:
        #then it should be part of a family with unbounded diameter
        #check if:
        # classical parameters
        # fold of (Johnson/half cube)
        # a near polygon
        pass
    elif d == 8:
        if arr == [3,2,2,2,2,1,1,1,1,1,1,1,2,2,2,3]:
            return GraphGenerators.FosterGraph()
        elif arr == [7,6,4,4,4,1,1,1,1,1,1,2,4,4,6,7]:
            return IvanovIvanovFaradjev_graph()
    elif d == 7:
        if arr == [3,2,2,2,1,1,1,1,1,1,1,1,1,3]:
            return GraphGenerators.BiggsSmithGraph()
        elif arr == [22,21,20,16,6,2,1,1,2,6,16,20,21,22]:
            return bipartite_double_graph(truncated_binary_Golay_code_graph())
        elif arr == [23, 22, 21, 20, 3, 2, 1, 1, 2, 3, 20, 21, 22, 23]:
            return bipartite_double_graph(binary_Golay_code_graph())
    elif d == 6:
        if arr == [21, 20, 16, 6, 2, 1, 1, 2, 6, 16, 20, 21]:
            return shortened_00_11_binary_Golay_code_graph()
        elif arr == [21, 20, 16, 9, 2, 1, 1, 2, 3, 16, 20, 21]:
            return shortened_000_111_extended_binary_Golay_code_graph()
        elif arr == [22, 21, 20, 3, 2, 1, 1, 2, 3, 20, 21, 22]:
            return shortened_binary_Golay_code_graph()
    elif d == 5:
        if arr == [3, 2, 1, 1, 1, 1, 1, 1, 2, 3]:
            return GraphGenerators.DodecahedralGraph()
        elif arr == [22, 20, 18, 2, 1, 1, 2, 9, 20, 22]:
            return shortened_extended_ternary_Golay_code_graph()
        elif arr == [7, 6, 6, 1, 1, 1, 1, 6, 6, 7]:
            return bipartite_double_graph(GraphGenerators.HoffmanSingletonGraph())
        elif arr == [10, 9, 8, 2, 1, 1, 2, 8, 9, 10]:
            return bipartite_double_graph(GraphGenerators.SimsGewirtzGraph())
        elif arr == [16, 15, 12, 4, 1, 1, 4, 12, 15, 16]:
            return bipartite_double_graph(GraphGenerators.strongly_regular_graph(77,16,0))
        elif arr == [22, 21, 16, 6, 1, 1, 6, 16, 21, 22]:
            return bipartite_double_graph(GraphGenerators.HigmanSimsGraph())
    elif d == 4:
        if arr == [3,2,2,1,1,1,1,2]:
            return Coxeter_graph()
        elif arr == [6,5,5,4,1,1,2,6]:
            return LintSchrijver_graph()
        elif arr == [7,6,4,4,1,1,1,6]:
            return doubly_truncated_Witt_graph()
        elif arr == [9,8,6,3,1,1,3,8]:
            return distance_3_doubly_truncated_Golay_code_graph()
        elif arr == [10,8,8,2,1,1,4,5]:
            return J2_graph()
        elif arr == [11,10,6,1,1,1,5,11]:
            return GraphGenerators.LivingstoneGraph()
        elif arr == [5,4,1,1,1,1,4,5]:
            return GraphGenerators.WellsGraph()
        elif arr == [6,4,2,1,1,1,4,6]:
            return Foster_graph_3S6()
        elif arr == [10,6,4,1,1,2,6,10]:
            return ConwaySmith_for_3S7()
        elif arr == [12,11,10,7,1,2,5,12]:
            #leonard graph
            pass
        elif arr == [20,18,4,1,1,2,18,20]:
            return shortened_ternary_Golay_code_graph()
        elif arr == [45,32,12,1,1,6,32,45]:
            return locally_GQ42_graph()
        elif arr == [117,80,24,1,1,12,80,117]:
            return graph_3O73()
    elif d == 3:
        #do something
        pass
    
    #otherwise check infinite families
    
    #classical parameters
    try:
        (d,b,alpha,beta) = get_classical_parameters_from_intersection_array( arr,True)
        return distance_regular_graph_with_classical_parameters(d,b,alpha,beta)
    except ValueError:
        #means can't do with classical paramaters
        pass

    (m,a) =  _is_pseudo_partition_graph( arr )
    if m != -1:
        return pseudo_partition_graph(m,a) #this may give errors
    # but there are no other graphs with such intersection arrays

    #gen 2d-gon
    (s,t) = is_generalised_2d_gon(arr)#this is not correct
    if s != -1:#valid gen 2d-gon
        if d == 6:
            return generalised_dodecagon(s,t)
            pass
        elif d == 4:
            return generalised_octagon(s,t)
        elif d == 3:
            return generalised_hexagon(s,t)

    #check near polygons
    #some classical parameters and pseudo partition graphs are near polygons, so it is
    #better to check those first and check near polygons later and assume that those cases can't arise
    if is_near_polygon(arr) != -1:
        return dist_reg_near_polygon(arr)

    raise ValueError("unknown graph")

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
from sage.arith.misc import is_prime_power
from sage.combinat.q_analogues import q_binomial
from sage.combinat.integer_vector import IntegerVectors
from sage.matrix.matrix_space import MatrixSpace
from sage.matrix.constructor import Matrix
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.modules.free_module import VectorSpace
from sage.modules.free_module_element import vector
from sage.rings.rational cimport Rational
from sage.rings.integer cimport Integer
from sage.combinat.designs import design_catalog as Sage_Designs
from sage.graphs.strongly_regular_db import strongly_regular_graph
from sage.combinat.subset import Subsets
from sage.sets.set import Set
from sage.libs.gap.libgap import libgap

from sage.graphs.distance_regular_codegraphs import *
from sage.graphs.distance_regular_sporadic import *

################################################################################
# UNBOUNDED DIAMETER

def doubled_odd_graph( int n ):
    r"""
    let X = {1,2,..., 2n +1}
    The doubled odd graph is the graph with
    V = subsets of X of size n, n+1
    E = { (s1,s2) | s1 in s2 or s2 in s1 }

    This is WAY faster than building odd graph via Sage and then doubling it
    """
    # construction:
    # get oll subsets of X of size n
    # for each such set s1, add a number not in s to create s2

    # if this is too slow, then construct as a hamming graph:
    # a binary vector of size 2n+1 represents a set
    cdef list edges = []
    for s1 in IntegerVectors(n,k=2*n +1, max_part=1):
        #s1 is a list
        #iterate through it and create s2
        for i in range(2*n+1):
            if s1[i] == 0:
                s2 = list(s1)
                s2[i] = 1
                #now s2 is a n+1-set containig s1
                edges.append((tuple(s1),tuple(s2)))

    G = Graph(edges, format='list_of_edges')
    G.name("Bipartite double of Odd graph on a set of %d elements"%(2*n+1))
    return G

def bilinear_form_graph(const int d, const int e, const int q):
    r"""
    Return a bilienar form graph with the given parameters.

    This build a graph whose vertices are all ``d``x``e`` matrices over
    ``GF(q)``. 2 vertices are adjecent if the difference of the 2 
    matrices has rank 1.

    INPUT:

    - ``d,e`` -- integers
    - ``q`` -- a prime power

    EXAMPLES:

    TESTS::
    
    """

    matricesOverq = MatrixSpace( GF(q), d, e, implementation='meataxe' )

    rank1Matrices = []
    for m in matricesOverq:
        sig_check()
        if m.rank() == 1:
            rank1Matrices.append(m)

    edges = []
    for m1 in matricesOverq:
        m1.set_immutable()
        for m2 in rank1Matrices:
            sig_check() # this loop may take a long time, so check for interrupts
            m3 = m1+m2
            m3.set_immutable()
            edges.append( ( m1, m3) )
    
    G = Graph(edges, format='list_of_edges')    
    G.name("Bilinear form graphs over F_%d with parameters (%d,%d)" %(q,d,e) )
    return G

def alternating_form_graph(const int n, const int q):
    r"""
    Return the alternating form graph with the given parameters.

    This construct a graph whose vertices are all ``n``x``n`` skew symmetric
    matrices over ``GF(q)`` with zero diagonal. 2 vertices are adjecent if and only if the
    difference of the 2 matrices has rank 2

    INPUT:

    - ``n`` -- integer
    - ``q`` -- prime power

    EXAMPLES:

        sage: g = alternating_form_graph(5,2)
        sage: g.is_distance_regular()
        True

    TESTS::

    """
    #import time

    def symmetry(x): return -x
    def diagonal(x): return 0

    matrices = MatrixSpace(GF(q), n, n, implementation="meataxe")

    #start = time.time()
    skewSymmetricMatrices = matrices.symmetric_generator(symmetry, diagonal)
    #end = time.time()
    #print("creating skewSymmetricMatrices %.6fs"%(end-start))

    #start = time.time()
    rank2Matrices = []
    for mat in skewSymmetricMatrices:
        sig_check()
        
        # finally check if mat is a rank2 matrix
        if mat.rank() == 2:
            rank2Matrices.append(mat) # we append v as it is smaller than mat
    #end = time.time()
    #print("found all rank 2 matrices in %.6f"%(end-start))
    
    #start = time.time()
    skewSymmetricMatrices = matrices.symmetric_generator(symmetry, diagonal)
    #end = time.time()
    #print("refresh skewSymmetricMatrices [it's a generator] %.6fs"%(end-start))
    
    # now we have all matrices of rank 2
    #start = time.time()
    edges = []
    for m1 in skewSymmetricMatrices:
        m1.set_immutable()
        for m2 in rank2Matrices:
            sig_check() # check for interrupts
            m3 = m1+m2
            m3.set_immutable()
            edges.append(( m1, m3 ))

    #end = time.time()
    #print("found all edges in %.6f"%(end-start))

    #start = time.time()
    G = Graph(edges, format='list_of_edges')
    #end = time.time()
    #print("constructed graph in %.6f"%(end-start))
    
    G.name("Alternating form graph on (F_%d)^%d" %(q,n) )
    return G    

def hermitean_form_graph(const int n, const int q):
    r"""
    Return the Hermitean from graph with the given parameters.

    We build a graph whose vertices are all ``n``x``n`` Hermitean matrices
    over ``GF(q)``. 2 vertices are adjecent if the difference of the 2 vertices
    has rank 1. We need ``q``=``r**2`` for some prime power ``r``

    INPUT:

    - ``n`` -- integer
    - ``q`` -- prime power

    EXAMPLES:

        sage: g = hermitean_form_graph(5,2)
        sage: g.is_distance_regular()
        True

    .. NOTES::
    
        If ``q`` does not satisfy the requirements, then this function
        will raise a ``ValueError``.
      
    TESTS::

    """
    MS = MatrixSpace(GF(q), n, n, implementation="meataxe")
    
    (b,k) = is_prime_power(q, True)
    if k == 0 or k % 2 != 0:
        raise ValueError("We need q=r^2 where r is a prime power")

    # here we have b^k = q, b is prime and k is even
    r = b**(k/2)
    # so r^2 = b^k = q

    def symmetry(x): return x**r

    hermiteanMatrices = MS.symmetric_generator(symmetry)

    rank1Matrices = []
    for mat in hermiteanMatrices:
        sig_check()
        if mat.rank() == 1: rank1Matrices.append(mat)

    #refresh generatro
    hermiteanMatrices = MS.symmetric_generator(symmetry)
    edges = []
    for mat in hermiteanMatrices:
        mat.set_immutable()
        for mat2 in rank1Matrices:
            sig_check()

            mat3 = mat + mat2
            mat3.set_immutable()
            edges.append( (mat, mat3) )

    G = Graph(edges, format='list_of_edges')
    G.name("Hermitean form graph on (F_%d)^%d" %(q,n) )
    return G
        
def halved_cube( int n ):
    r"""
    Return the graph $\frac 1 2 Q_n$.

    This builds the halved cube graph in ``n`` dimensions.
    The construction is iterative, so the vertices label have no meaning.
    
    INPUT:

    - ``n`` -- integer

    EXAMPLES:

        sage: g = halved_cube(8) # long time for large n

        # n = 14 -> ~1min
        # n = 15 -> ~4min

        sage: g.is_distance_regular()
        True

    TESTS::

    """
    def hamming_distance( v, w ):
        assert( len(v) == len(w),
         "Can't compute Hamming distance of 2 vectors of different size!")
         
        cdef int counter = 0
        for i in range(len(v)):
            if ( v[i] != w[i] ):
                counter = counter + 1
    
        return counter

    #construct the halved cube graph 1/2 Q_n ( = Q_{n-1} ^2 )
    G = GraphGenerators.CubeGraph(n-1)
    # now square the graph
    # we use the fact that the vertices are strings and their distance is their hamming_distance
    for i in G.vertices():
        for j in G.vertices():
            sig_check()
            if hamming_distance(i, j) == 2 :
                G.add_edge(i,j)
                
    G.relabel() # label back vertices to 0,1,2,...

    G.name("Halved %d Cube"%n)
    return G        
    


def Grassman( const int q, const int n, const int input_e ):
    r"""

    Return a Grassman graph with parameters ``(q,n,e)``.

    This build the Grassman graph $J_q(n,e)$. That is, for a vector
    space $V = \mathbb F(q))^n$ the output is a graph on the subspaces
    of dimension $e$ where 2 subspaces are adjancent if their intersection
    has dimension $e-1$.

    INPUT:
   
    - ``q`` -- a prime power
    - ``n, e`` -- integers with ``n >= e``

    EXAMPLES:

        tbd

    TESTS::

        tbd

    """
    if n < input_e:
        raise ValueError(
            "Impossible parameters n > e (%d > %d)" %(n,input_e) )
    
    e = input_e
    if n < 2*input_e:
        e = n - input_e
        
    
    PG = Sage_Designs.ProjectiveGeometryDesign(n-1, e-1, q)
    #we want the intersection graph
    #the size of the intersection must be (q^{e-1} - 1) / (q-1)
    cdef int size = (q**(e-1) -  1)/(q-1)
    G = PG.intersection_graph([size])
    G.name("Grassman graph J_%d(%d,%d)"%(q,n,e))
    return G

def double_Grassman(const int q, const int n, const int e):
    r"""
    vertices : e, e+1 dimensional subsets of (F_q)^n
    edges: (u,v) if u\neq v and (u \in v or v \in u)
    """

    PG1 = Sage_Designs.ProjectiveGeometryDesign(n-1,e-1,q)
    PG2 = Sage_Designs.ProjectiveGeometryDesign(n-1,e,q)

    edges = []
    for b in PG1.blocks():
        b1 = frozenset(b)
        for b2 in PG2.blocks():
            if b1.issubset(b2):
                edges.append( (b1,frozenset(b2)) )

    G = Graph(edges,format='list_of_edges')
    G.name("Double Grassman graph (%d,%d,%d)"%(n,e,q))
    return G

################################################################################
# UNBOUNDED ORDER

def gen_quadrangle2(q):
    "return the quadrangle Q(5,q)"
    Fq = GF(q)
    V = VectorSpace(Fq,6)

    if q % 2 == 1:
        b = 0
        c = - Fq.primitive_element()
    elif q == 2:
        b = 1
        c = 1
    else:
        c = 1
        elems = set([x for x in Fq])
        for x in Fq:
            if x == 0: continue
            try:
                elems.remove( x+ 1/x)
            except KeyError: #x+1/x not in elems which is ok
                pass
        b = elems.pop()#any of this will do
    
    def quadric(v):
        res = v[0]*v[0]+v[2]*v[3] + v[4]*v[5]
        res += b*v[0]*v[1] + c*v[1]*v[1]
        return res

    points = []
    for P in V.subspaces(1):
        v = P.basis()[0]
        if quadric(v) == 0:
            points.append(v)
    print("done points")
    
    lines = []
    for L in V.subspaces(2):
        line = []
        lineSize = 0
        for p in points:
            if p in L:
                line.append(p)
                lineSize+= 1
            if lineSize == q+1: break
        if line :
            lines.append(line)
    print("done lines")
    from sage.combinat.designs.incidence_structures import IncidenceStructure
    D = IncidenceStructure(points= points, blocks = lines)
    return D
    

def gen_quadrangle(q):
    "return the quadrangle H(3,q^2)"
    def h(v):
        res = 0
        for x in v:
            res += x**(q+1)
        return res

    V = VectorSpace(GF(q**2),4)
    points = [ ]
    for P in V.subspaces(1):
        v = P.basis()[0]
        if h(v) == 0:
            points.append(v)

    #points = [ p | h(p) == 0] and p is a point in the projective space

    lines = []
    for L in V.subspaces(2):
        #L is a line
        line = []
        for p in points:
            if p in L:
                line.append(p)
        if line:
            lines.append(line)

    #now we have points and lines
    from sage.combinat.designs.incidence_structures import IncidenceStructure
    D = IncidenceStructure(points= points, blocks = lines)
    return D


def unitary_nonisotropic_graph(q):
    r"""
    see page 383 on BCN
    """

    #hermitean form
    def h(u,v):
        w = [ x**q for x in v]#conjugate of v
        return u[0]*w[0]+u[1]*w[1]+u[2]*w[2]

    r = q*q
    V = VectorSpace(GF(r),3)

    vertices = [] #projective points that are nonisotropic
    for P in V.subspaces(1):
        v = P.basis()[0]
        if h(v,v) != 0:
            vertices.append(v)

    for v in vertices:
        v.set_immutable()

    n = len(vertices)
    edges = []
    for i in range(n):
        v = vertices[i]
        for j in range(i+1,n):
            w = vertices[j]
            if h(v,w) == 0:
                edges.append((v,w))

    G = Graph(edges,format="list_of_edges")
    G.name("Unitary nonisotropic graph on (F_%d)^3"%r)
    return G

def graph_from_two_design( D ):
    r"""
    Given a two graph (block design) it builds a graph associated with it.
    """

    edges = []
    
    #vertices = x^+, x^- for all x\in X
    # x^a,y^b are adjecent if: x != y and ( (a == b and {x,y,inf} coherent) or ( a != B and {x,y,inf} not coherent) )
    # inf is just a point in X
    inf = D.ground_set()[0]

    #first we do all coherent edges
    S = set() #set of coherent pairs
    for b in D.blocks():
        if b[0] == inf: x=b[1]; y=b[2]
        elif b[1] == inf: x=b[0]; y=b[2]
        elif b[2] == inf: x=b[0];y=b[1]
        else: continue
        #now x,y,inf are coherent
        S.add( frozenset([x,y]) )
        edges.append( ((x,0),(y,0)) )
        edges.append( ((x,1),(y,1)) )

    #inf is coherent with any other vertex!!
    for x in D.ground_set()[1:]:#we don't want edge inf inf
        #{x,inf,inf} is coherent
        edges.append( ((x,0),(inf,0)) )
        edges.append( ((x,1),(inf,1)) )
        S.add( frozenset([x,inf]) )

    #now we can handle the non-coherent ones
    l = D.num_points()
    for i in range(l):
        x = D.ground_set()[i]
        for j in range(i+1,l):#go through all ordered pairt
            y = D.ground_set()[j]
            if frozenset([x,y]) in S: continue#x,y,inf coherent
            #otherwise add edge
            edges.append( ((x,0),(y,1)) )
            edges.append( ((x,1),(y,0)) )

    G = Graph(edges,format="list_of_edges")
    return G

def symmetric_net_incident_graph(m,u):
   SN = Sage_Designs.symmetric_net(m,u)
   return SN.incidence_graph()


def generalised_dodecagon(s,t):
    cdef int q = 0
    cdef int orderType = 0

    if s == 1: #(1,q)
        q = t
    elif t == 1: # (q,1)
        q = s
        orderType = 1
    else:
        raise ValueError("invalid input")

    if not is_prime_power(q):
        raise ValueError("invalid input")

    if orderType == 0:
        #incidence graph of hexagon (q,q)
        
        H = generalised_hexagon(q,q)
        lines = extract_lines(H,q,q)
        points = list(H.vertices())

        edges = []
        for p in points:
            for l in lines:
                if p in l:
                    edges.append( (p,l) )

        G = Graph(edges, format='list_of_edges')
        G.name("Generalised dodecagon of order (1,%d)"%q)
        return G
    
    else: #orderType == 1
        #dual
        H = generalised_dodecagon(t,s)
        G = line_graph_generalised_polygon(H,t,s)
        G.name("Generalised dodecagon of order (%s,%d)"%(s,t))
        return G
    
        

def generalised_octagon(s,t):
    cdef int q = 0
    cdef int orderType = 0
    if s == 1:# (1,q)
        q = t
    elif t == 1:# (q,1)
        q = s
        orderType = 1
    elif s**2 ==  t:# (q,q^2)
        q = s
        orderType = 2
    elif t**2 == s: #(q^2,q)
        q = t
        orderType = 1
    else:
        raise ValueError("invalid input")

    if not is_prime_power(q):
        raise ValueError("invalid input")

    if orderType == 0:
        H = strongly_regular_graph((q+1)*(q*q+1),q*(q+1),q-1,q+1)
        # above is pointgraph of generalised quadrangle (q,q)
        lines = extract_lines(H,q,q)
        points = list(H.vertices())
        #points and lines make the quadrangle

        edges = []
        for p in points:
            for l in lines:
                if p in l:
                    edges.append( (p,l) )

        G = Graph(edges, format='list_of_edges')
        G.name("Generalised octagon of order (1,%d)"%q)
        return G
        
    elif orderType == 1:
        #dual
        H = generalised_octagon(t,s)
        G = line_graph_generalised_polygon(H,t,s)
        G.name("Generalised octagon of order(%d,%d)"%(s,t))
        return G
    else:
        if q == 2:
            g = libgap.AtlasGroup("2F4(2)", libgap.NrMovedPoints, 1755)
            G = Graph( g.Orbit( [1,73], libgap.OnSets), format='list_of_edges')
            G.name("Generalised octagon of order (2,4)")
            return G
        else:
            pass
    pass
         
    
    
def extract_lines( G, s, t):
    r"""given the point graph of a generalised 2d-gon of order (s,t) we
    extract the lines from G and return it

    all lines lies on s+1 points
    all points are incident to t+1 lines

    a line is a clique of size s+1
    a maximal clique of size s+1 must be a line (since all points are on at least 1 line)

    we know that number of points |V(G)|, hence the number of lines is |V(G)|*(t+1)/(s+1)

    NOOOO above is fine, but we should do this way:
    Let (x,y) be an edge,
    then {x,y}^bottom^bottom is a singular line (we want singular lines)
    we define x^bottom = neighbours of x and x
              S^bottom = intersection of x^bottom for all x in S
    """

    numLines = (G.order() * (t+1)) / (s+1)

    lines = []
    edges = set(G.edges(sort=False))
    
    while edges :
        (x,y,w) = edges.pop()

        #compute line
        bottomX = set(G.neighbors(x,closed=True))
        bottomY = set(G.neighbors(y,closed=True))
        bottom1 = bottomX.intersection(bottomY)

        b = bottom1.pop()
        bottom2 = frozenset(G.neighbors(b,closed=True))
        for v in bottom1:
            s = frozenset(G.neighbors(v,closed=True))
            bottom2 = bottom2.intersection(s)

        #now bottom2 is a line
        lines.append(bottom2)
        
        #remove pointless edges
        for u in bottom2:
            for v in bottom2:
                try :
                    edges.remove( (u,v,None) )
                except KeyError:
                    pass #ignore this
                
    #loop to next edge

    return lines



def line_graph_generalised_polygon(H, s,t):
    r"""
    Given the point graph H of a generalised n-gon of order (s,t)
    it returns the point graph of a generalised n-gon of order (t,s)
    """
    lines = extract_lines(H,s,t)

    edges = []
    n = len(lines)
    for i in range(n):
        l1 = lines[i]
        for j in range(i+1,n):
            l2 = lines[j]
            if l1.intersection(l2) :
                edges.append( (l1,l2) )
            
    G = Graph(edges, format='list_of_edges')
    return G
    

def generalised_hexagon( const int s, const int t):
    cdef int q = 0
    cdef int orderType = 0
    if s == 1: # (1,q)
        q = t
    elif t == 1:# (q,1)
        q = s
        orderType = 1
    elif s == t:# (q,q)
        q = s
        orderType = 2
    elif s**3 == t:# (q,q^3)
        q = s
        orderType = 3
    elif t**3 == s: # (q^3, q)
        q = t
        orderType = 1
    else:
        raise ValueError("invalid input")

    if not is_prime_power(q):
        raise ValueError("invalid input")

    if orderType == 0:
        #incident graph of generalised 3-gon of order (q,q)
        V = VectorSpace(GF(q),3) #generalised triangle
        points = list(V.subspaces(1))
        lines = list(V.subspaces(2))

        edges = []
        for p in points:
            pb = p.basis_matrix()
            for l in lines:
                if p.is_subspace(l):
                    edges.append( (pb, l.basis_matrix()) )

        G = Graph(edges, format='list_of_edges')
        G.name("Generalised hexagon of order (1,%d)"%q)
        return G#G.edges() gives problems
        
    elif orderType == 1:
        # "dual" graph 
        H = generalised_hexagon(t,s)
        G = line_graph_generalised_polygon(H,t,s)
        G.name("Generalised hexagon of order(%d,%d)"%(s,t))
        return G
        
    elif orderType == 2:
        # we use the group G2(q)
        # if q == 2, then G2(2) is isomorphic to U3(3).2
        if q == 2:
            group = libgap.AtlasGroup("U3(3).2", libgap.NrMovedPoints, 63)
            G = Graph( group.Orbit([1,19], libgap.OnSets), format='list_of_edges')
            G.name("Generalised hexagon of order (%d,%d)"%(q,q))
            return G
        elif q == 3: #we don't have permutation rep
            matrixRep = libgap.AtlasGroup("G2(3)", libgap.Position,7)
            e1 = vector(GF(3), [1,0,0,0,0,0,0])
            orb = matrixRep.Orbit(e1, libgap.OnLines)
            group = libgap.Action(matrixRep,orb,libgap.OnLines)
            #now group is our permutation rep
            G = Graph(group.Orbit([1,52], libgap.OnSets), format='list_of_edges')
            G.name("Generealised hexagon of order (%d,%d)"%(q,q))
            return G
        else:
            arr = intersection_array_2d_gon(3,s,t)
            n = number_of_vertices_from_intersection_array(arr)
            G = graph_from_permutation_group( libgap.AtlasGroup("G2(%d)"%q, libgap.NrMovedPoints, n), arr[0])
            G.name("Generalised hexagon of order (%d,%d)"%(q,q))
            return G
        pass
    elif orderType == 3:
        pass
    pass


def graph_from_permutation_group( group, order ):
    r"""
    construct graph whose automorphism group is "group"
    we ensure the graph has order "order"
    "group" should be a GAP group
    we also require 1 to be in the graph
    """

    h = group.Stabilizer(1)
    orbitIndex = 0
    orbitLenghts = h.OrbitLengths()

    # if we can't find the correct orbit, we can out of bound error
    while orbitLenghts[orbitIndex] != order:
        orbitIndex += 1

    #now we found the correct orbit
    v = h.Orbits()[orbitIndex][0] #pick an element of the orbit

    G = Graph( group.Orbit( [1,v], libgap.OnSets), format='list_of_edges')

    return G

def graph_3D42(const int q):
    r"""
    we build the graph $^3D_{4,2}(q)$. Those come from the groups $^3D_4(q)$

    requires gap and gap_packages
    """

    if q>3:
        raise ValueError("graph not implemented yet")
    if q < 2:
        raise ValueError("input should be either 2 or 3")
    
    libgap.eval("SetInfoLevel(InfoWarning,0)") # silence #I warnings from GAP (without IO pkg)
    libgap.LoadPackage("AtlasRep")

    if q == 2:
        group = libgap.AtlasGroup("3D4(2)",libgap.NrMovedPoints,819)
    else:
        group = libgap.AtlasGroup("3D4(3)",libgap.NrMovedPoints,26572)
    
    libgap.eval("SetInfoLevel(InfoWarning,1)") # restore #I warnings

    graph = Graph(group.Orbit([1,2],libgap.OnSets), format='list_of_edges')
    
    graph.name("Triality graph ^3D_{4,2}(%d)"%(q))
        
    return graph


def coset_graph( const int q, C_basis, U_basis = None, n = None ):
    r"""
    computes the coset graph \Gamma(C) where C = span(C_basis)
    we need U = span(U_basis) to be s.t. U+C = V
    all vector spaces are over GF(q) and V has dimension n
    """

    if n == None:
        n = len(C_basis[0])# dim V
    F = GF(q) #base field

    if U_basis == None:
        V = VectorSpace(F,n)
        C = V.span(C_basis)
        Q = V.quotient(C)
        lift = Q.lift_map()
        U_basis = [ lift(v) for v in Q.basis() ]

    lambdas = [ x for x in F if x != 0 ]#non-zero elements of F
    
    def e(const int i):
        v = [0]*n
        v[i-1] = 1
        return vector(F,v)

    V = VectorSpace(F,n)
    U = V.span(U_basis)

    vertices = list(U)

    # build our matrix A
    A = U_basis.copy()
    for c in C_basis:
        A.append(c)

    A = Matrix(F,A)
    A = A.transpose()
    #now A is done

    Ainv = A.inverse()

    ui = [] #list of P(e_i)
    for i in range(n+1):
        ei = e(i)
        if ei in U_basis:
            ui.append(ei)
        else:
            a = Ainv * ei
            # get zero vector and sum a[i]u_i to it
            v = [0]*n
            v = vector(F,v)
            for i in range(len(U_basis)):
                v += a[i]*U_basis[i]
            ui.append(v)

    #now we are ready to build all the edges
    edges = []
    for v in vertices:
        vt = tuple(v)
        for x in ui:
            for l in lambdas:
                w = v+ l* x
                edges.append( (vt, tuple(w)) )

    G = Graph(edges, format='list_of_edges')
    return G

def extended_Kasami_code(s,t):
    #check s,t are good
    
    F2 = GF(2)
    V = VectorSpace(F2, s)
    elemsFs = [x for x in GF(s)]
    FsToInt = { x : i for i,x in enumerate(elemsFs)}
    elemsFsT = [x**(t+1) for x in elemsFs]
    FsTToInt = { x: i for i,x in enumerate(elemsFsT)}

    e1 = [0]*s
    e1[0] = 1
    e1 = vector(F2,e1,immutable=True)
    assert(e1 in V, "e1 not in V!")

    W1_basis = []
    for i in range(s-1):
        v = [0]*s
        v[i] = 1
        v[s-1] = 1
        W1_basis.append(v)
    W1 = V.span(W1_basis) #W satisfies \sum v[i] = 0

    W2_basis = set([e1])#not really a basis...
    for i in range(1,s):#avoid x = 0
        x = elemsFs[i]
        for j in range(i+1,s):
            y = elemsFs[j]
            v = [0]*s
            v[i] = 1
            v[j] = 1
            v[ FsToInt[(x+y)] ] = 1
            v = vector(F2,v,immutable=True)
            W2_basis.add(v)
    W2 = V.span(W2_basis) #U satisfies \sum v[i]elemsFs[i] = 0


    W3_basis = set([e1]) #again not really a basis
    for i in range(1,s): #avoid x = 0^(t+1) = 0
        x = elemsFsT[i]
        for j in range(i+1,s):
            y = elemsFsT[j]
            v = [0]*s
            v[i] = 1
            v[j] = 1
            v[ FsTToInt[(x+y)] ] = 1
            v=vector(F2,v,immutable=True)
            W3_basis.add(v)
    W3 = V.span(W3_basis)

    W = W2.intersection(W3)
    codebook = W.intersection(W1)
    
    return codebook

def Kasami_code(s,t):
    r"""
    take extended Kasami and truncate it
    """

    C = extended_Kasami_code(s,t)
    codebook = [v[1:] for v in C.basis()]
    V = VectorSpace(GF(2),s-1)
    
    return V.span(codebook)

def Kasami_graph(s,t):
    K = Kasami_code(s,t)
    G = coset_graph(2,K.basis(),n=s-1)
    G.name("Coset graph of Kasami code (%d,%d)"%(s,t))
    return G

def extended_Kasami_graph(s,t):
    K = extended_Kasami_code(s,t)
    G = coset_graph(2,K.basis(), n=s)
    G.name("Coset graph of extended Kasami code (%d,%d)"%(s,t))
    return G


################################################################################
# UTIL FUNCTIONS

def number_of_vertices_from_intersection_array( array ):
    cdef int d = len(array) / 2

    cdef int ki = 1
    cdef int v = 1
    # invariant v = sum([k_0,..,k_i))
    for i in range(1,d+1):
        ki = (ki*array[i-1]) / array[d+i-1] # k_{i+1} = k_i*b_i /c_{i+1}
        v += ki

    return v

# from bouwer book, we assume d \gt 3 [not sure if it works with smaller d]
def intersection_array_from_classical_parameters( const int d,
                                                  const int b,
                                                  alpha,
                                                  beta ):
    r"""
    Return the intersection array generated by the input.

    The input represents the classical parameters $(d,b,\alpha,\beta)$.
    The result is the intersection array of a possible graph with such parameters.
    Note that we don't check for the existance of such graph.

    INPUT:
    - ``d, b`` -- integers
    - ``alpha, beta`` -- numbers

    EXAMPLES:

        tbd

    ..NOTE::
    
        Atm we don't knwo if this works for d< 3

    TESTS::

        tbd
    """
    if b == 1:
        bs = [ d *beta ] #bs will be the list {b_0, ..., b_{d-1} }
    else:
        bs = [ (b**d -1)/(b-1) * beta ]
    
    cs = [ ] # cs will be the list {c_1, ..., c_d }
    btoi = 1 # this represents b^i and it is only used if b \neq 1
    btod = b ** d # b^d used when b \neq 1
    invb = 1 #this represents 1 / b - 1 in case b \neq 1
    if b != 1 : invb = Rational(1.0 / (b - 1.0))
    for i in range(1,d):
        if b == 1: #easy formula if b is 1
            bs.append( (d - i) * (beta - alpha * i) )
            cs.append( i * (1 + alpha * (i - 1)) )
        else :
            # 1+ \a \frac {b^{i-1} - 1}{b - 1}
            c = 1 + alpha * ( btoi - 1 ) * invb
            btoi = btoi * b
            c = c * (btoi - 1) * invb # c = c_i
            cs.append( c )
            bs.append( invb * (btod - btoi) * (beta - alpha*(btoi - 1)*invb) )
            
    # now we need to add c_d to cs
    if b == 1:
        cs.append( d * (1 + alpha * (d - 1)) )
    else :
        c = 1 + alpha * ( btoi - 1 ) * invb # 1+ \a \frac {b^{d-1} - 1}{b - 1}
        c = c * (btod - 1) * invb # c = c_d
        cs.append( c )
    return (bs + cs)

def intersection_array_from_graph( G ):
    r"""
    Return the intersection array of this graph.

    This function is a simple wrapper around 
    :meth:`sage.graphs.distances_all_pairs.is_distance_regular`
    but it returns the intersection array
    $\{b_0,...,b_{d-1},c_1,...,c_d\}$.
    If the input is not a distance-regular graph, then
    a ``ValueError`` is raised.

    INPUT:
    
    - ``G`` -- a distance-regular graph

    EXAMPLES:

        tbd
    
    ..NOTE::

        A ``ValueError`` will be raised if the input graph is not
        distance-regular.
    """
    t = G.is_distance_regular(True)
    if not t:
        raise ValueError("the graph passed is not distance_regular")
    (b,c) = t
    # annoyingly b ends with None (b_d = 0)
    # and c starts with None (c_0 = 0)
    # so trim these 2 values
    return b[:-1]+c[1:]

def get_classical_parameters_from_intersection_array( array, check=False):
    r"""
    Return the classical parameters ``(d,b,alpha,beta)`` 
    representing the intersection array.

    This function will check whether given array is an itersection array 
    that can be represented with classical parameters.
    You can disable these extra checks, by setting the optional check input
    to ``False``

    INPUT:

    - ``array`` -- array of integers
    - ``check`` -- boolean; if ``False`` this function will assume that 
      ``array`` is a valid intersection array

    OUTPUT:
    
    tuple ``(d,b,alpha,beta)`` of classical parameters for array.

    EXAMPLES:

        tbd

    ALGORITHM:

    This algorithm takes advantage of theorem 6.2.1 on page 195 of bouwer book
    

    .. NOTE::

        This function may raise a ``ValueError`` if ``check`` is set to ``True``.

    TESTS::

        tbd

    """
    # b_i = arr[i]; c_i = arr[d - 1 + i]
    if check and len(array) % 2 != 0 : return False
    
    d = len(array) / 2

    def c_( const int i ) :
        if i == 0: return 0
        return array[d-1 + i]

    def b_( const int i ) :
        if i == d: return 0
        return array[i]

    def a_( const int i ):
        return array[0] - b_(i) - c_(i) 

    def getAlphaBeta(const int b):
        return  ( c_(2) / (b + 1) - 1, array[0] / q_binomial(d,1,q=b) )

    def checkValues(arr, const int d, const int b, alpha, beta):
        trial = intersection_array_from_classical_parameters(d, b, alpha, beta)
        for i in range(2*d):
            if trial[i] != arr[i] : return False
        
        return True
    
    case1 = True # assume we are in the case a_i != a_1 * c_i
    for i in range(2,d): # yes, 2 is intentional
        # if a_i == a_1 * c_i
        if a_(i)  == a_(1) * c_(i): 
            case1 = False
            break
        
    if case1:
        # b = (a_2*c_3 - c_2*a_3)/(a_1*c_3 - a_3)
        b = ( a_(2) * c_(3) - c_(2) * a_(3)) / ( a_(1) * c_(3) - a_(3) )
    else :
        # b \in { c_2 - 1, -a_1 - 1}
        # try b = c_2 - 1
        b = c_(2) - 1
        if b not in {0,-1} and q_binomial(d,1,q=b) != 0:#look at p196 for reasons why 0,-1
            (alpha,beta) = getAlphaBeta(b)
            if not checkValues(array, d, b, alpha, beta) :
                # then we must have b = -a_1 - 1
                b = -a_(1) - 1
        else:
            # then we must have b = -a_1 - 1
            b = -a_(1) - 1

    if b in {0,-1} or q_binomial(d,1,q=b) == 0:
        raise ValueError("invalid input")
    
    (alpha,beta) = getAlphaBeta(b)
    
    if check and not checkValues(array, d, b, alpha, beta):
        raise ValueError(
            "Input array can't be represented with classical parameters")
    
    return (d, b, alpha, beta)

def intersection_array_of_pseudo_partition_graph(m,a):
    r"""
    Return intersection array of pseudo partiotion graph with parameters m,a

    m = 2*d or 2*d +1
    b_i = (m-i)(1 + a(m-1-i)) for i < d
    c_i = i(1+ a(i-1)) for i < d
    b_d = 0; c_d = g*d(1+a(d-1)) where g = m % 2
    """
    g = 2 - m% 2
    if g == 2:
        d = m // 2
    else:
        d = (m-1) // 2

    arr = [0]*(2*d)
    for i in range(d):
        arr[i] = (m - i)*( 1 + a*(m-1-i)) #b_i
        j = i+1
        arr[i+d] = j*(1+a*(j-1)) #c_j

    arr[2*d-1] = g*d*(1+a*(d-1)) #fix c_d

    return arr

def is_pseudo_partition_graph( list arr ):
    r"""
    returns (m,a) if arr is the intersection array of a spuedo partition graph with parameters m,a
    if the array is no good, then returns (-1,-1)
    p197

   

    """
    d = len(arr)
    if d % 2 != 0:
        raise ValueError("incorrect intersection array given")

    d = d // 2

    if d < 3 :
        raise ValueError("only deal with distance regular graphs of diameter >= 3")
    
    #m = 2*d or 2*d +1
    #b_i = (m-i)(1 + a(m-1-i)) for i < d
    #c_i = i(1+ a(i-1)) for i < d
    #b_d = 0; c_d = g*d(1+a(d-1)) where g = m % 2

    #c_2 = 2 ( 1+a)
    c2 = arr[d+1]
    if c2 % 2 != 0:
        return (-1,-1)
    a = c2 // 2 -1

    #try m = 2d
    m = 2*d

    newArr = intersection_array_of_pseudo_partition_graph(m,a)
    if arr == newArr:
        return (m,a)
    else:
        m = m+1# m = 2*d +1
        newArr = intersection_array_of_pseudo_partition_graph(m,a)
        if arr == newArr:
            return (m,a)

    return (-1,-1)

def is_near_polygon(list arr):
    r"""
    Checks if the intersection array could be of a near polygon. if so returns a parameter l, otherwise -1

    p199 theorem 6.4.1:
    a dist-reg graph with int. arr [b_0,...,b_{d-1}, c_1, ..., c_d] is a regular near polygon
    iff there is no induced subgraph K_{1,1,2} and there is l s.t. b_i = k - (l+1)*c_i for i = 0,..,d-1.

    In particular, if it is a near polygon, then is a near 2d-gon if k = (l+1)*c_d and a near (2d+1)-gon otherwise
    """

    d = len(arr)
    if d % 2 != 0:
        raise ValueError("intersection array can't be one of a dist. reg. graph")
    d = d // 2

    k = arr[0]
    l = (k - arr[1]) // arr[d] - 1
    
    #for i = 0 we have b_0 = k - (l+1)*c_0 = k since c_0 = 0 always
    # we check i = 1 since in our expression for l we use integer division
    for i in range(1,d-1):
        if arr[i] != k - (l+1)*arr[d+i-1]:
            return -1

    #if we get here we passed the test
    return l

def intersection_array_2d_gon(d, s, t):
    b = [0]*d
    c = [0]*d

    b[0] = s*(t+1)
    c[d-1] = t+1

    for i in range(d-1):
        c[i] = 1

    for i in range(1,d):
        b[i] = b[0] - s

    return b + c



################################################################################
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
        
        return GraphGenerators.CycleGraph(n)

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

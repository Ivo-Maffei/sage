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

from sage.categories.sets_cat import EmptySetError
from sage.misc.unknown import Unknown

from sage.graphs.distance_regular_codegraphs import coset_graph
from sage.graphs.distance_regular_sporadic import *
from sage.graphs.distance_regular_related_objects import (distance_regular_association_scheme,
                                                          two_graph, Kasami_code, extended_Kasami_code,
                                                          generalised_quadrangle_with_spread)

################################################################################
# UNBOUNDED DIAMETER
                
def Ustimenko_graph(m,q):
    r"""
    dist 1-or-2 of the dual polar graph C_{m-1}(q)

    classical with parameters (d,q^2, qbinom(3,1,q) -1, qbinom(m+1,1,q) -1)
    """

    G = GraphGenerators.SymplecticDualPolarGraph(2*m-2,q)

    edgesToAdd = []
    #we can't add edges as we go since this will change the distances in the graph
    for v in G.vertices():
        for w in G.neighbors(v):
            for u in G.neighbors(w):
                if u != v and not G.has_edge(u,v):
                    #then u,v are at distance 2
                    edgesToAdd.append( (u,v) )

    G.add_edges(edgesToAdd)
    return G

def dual_polar_orthogonal(const int e, const int  d, const int q):
    r"""
    Return dual polar graph on $GO^e(n,q)$ of diameter d

    Inputs: e, d, q
    
    n is determined by d and e
    """

    def hashable(v):
        v.set_immutable()
        return v

    if e not in {0,1,-1}:
        raise ValueError("e must by 0,+1 or -1")

    m = 2*d + 1 - e

    group = libgap.GeneralOrthogonalGroup(e,m,q)
    M = Matrix(libgap.InvariantQuadraticForm(group)["matrix"])
    #Q(x) = xMx is our quadratic form

    #we need to find a totally isotropic subspace of dimension d
    #attempt 1 (consider kernel)
    K = M.kernel()
    isotropicBasis = list(K.basis())
    
    #extend K to a maximal isotropic subspace
    if K.dimension() < d:
        V = VectorSpace(GF(q),m)
        candidates = set(map(hashable,[P.basis()[0] for P in V.subspaces(1)]))#all projective points
        hashableK = map(hashable, [P.basis()[0] for P in K.subspaces(1)])
        candidates = candidates.difference(hashableK) #remove all points already in K
        nonZeroScalars = [ x for x in GF(q) if not  x.is_zero() ]
        while K.dimension() < d:
            found = False#found vector to extend K?
            while not found:
                v = candidates.pop()
                if v*M*v == 0:
                    #found another isotropic point
                    #check if we can add it to K
                    found  = True
                    for w in isotropicBasis:
                        if w*M*v+v*M*w != 0:
                            found  = False
                            break
            #end while found
            isotropicBasis.append(v)
            #remove new points of K
            newVectors = map(hashable,[ k+l*v for k in K for l in nonZeroScalars ])
            candidates.difference(newVectors)
            K = V.span(isotropicBasis)
        #end while K.dimension
        isotropicBasis = list(K.basis())

    W = libgap.FullRowSpace(libgap.GF(q), m) #W is GAP version of V
    isoS = libgap.Subspace(W,isotropicBasis) #isoS is GAP version of K

    allIsoPoints = libgap.Orbit(group,isotropicBasis[0],libgap.OnLines) #all isotropic projective points
    permutation = libgap.Action(group, allIsoPoints,libgap.OnLines)
    #this is the permutation group generated by GO^e(n,q) acting on projective isotropic points

    #translate K(=isoS) to int for the permutation group
    isoSPoints = [libgap.Elements(libgap.Basis(x))[0] for x in libgap.Elements(isoS.Subspaces(1))]
    isoSPointsInt = libgap.Set([libgap.Position(allIsoPoints, x) for x in isoSPoints])

    allIsoSubspaces = libgap.Orbit(permutation,isoSPointsInt, libgap.OnSets)#our vertices
    intersection_size = (q**(d-1) - 1) / (q-1) #number of projective points in a d-1 subspace

    edges = []
    n = len(allIsoSubspaces)
    for i in range(n):
        seti = allIsoSubspaces[i]
        for j in range(i+1,n):
            setj = allIsoSubspaces[j]
            if libgap.Size(libgap.Intersection(seti,setj)) == intersection_size:
                edges.append( (i,j) )

    G = Graph(edges, format="list_of_edges")
    G.name("Dual Polar Graph on Orthogonal group (%d,%d,%d)"%(e,m,q))
    return G


def doubled_odd_graph( const int n ):
    r"""
    Double odd graph on 2*n+1 points

    Input: n
    """

    if n < 1:
        raise ValueError("n must be >= 1")
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
            sig_check()
            if s1[i] == 0:
                s2 = list(s1)
                s2[i] = 1
                #now s2 is a n+1-set containing s1
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

    classical (\min (d,e), q, q-1 , q^{\max(d,e)}-1)

    need sage -i meataxe

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

    classical ( n//2,  q^2, q^2-1, q^{2 ceil(n/2) -1})

    INPUT:

    - ``n`` -- integer
    - ``q`` -- prime power

    EXAMPLES:

        sage: g = alternating_form_graph(5,2)
        sage: g.is_distance_regular()
        True

    TESTS::

    """

    def symmetry(x): return -x
    def diagonal(x): return 0

    matrices = MatrixSpace(GF(q), n, n, implementation="meataxe")
    skewSymmetricMatrices = matrices.symmetric_generator(symmetry, diagonal)

    rank2Matrices = []
    for mat in skewSymmetricMatrices:
        sig_check()
        # check if mat is a rank2 matrix
        if mat.rank() == 2:
            rank2Matrices.append(mat)
    
    skewSymmetricMatrices = matrices.symmetric_generator(symmetry, diagonal)
    
    # now we have all matrices of rank 2
    edges = []
    for m1 in skewSymmetricMatrices:
        m1.set_immutable()
        for m2 in rank2Matrices:
            sig_check() # check for interrupts
            m3 = m1+m2
            m3.set_immutable()
            edges.append(( m1, m3 ))

    G = Graph(edges, format='list_of_edges')
    G.name("Alternating form graph on (F_%d)^%d" %(q,n) )
    return G    

def hermitian_form_graph(const int n, const int q):
    r"""
    Return the Hermitian from graph with the given parameters.

    We build a graph whose vertices are all ``n``x``n`` Hermitian matrices
    over ``GF(q)``. 2 vertices are adjecent if the difference of the 2 vertices
    has rank 1. We need ``q``=``r**2`` for some prime power ``r``

    classical (n, -sqrt{q}, -sqrt{q}-1, - (- sqrt{q})^d -1)

    INPUT:

    - ``n`` -- integer
    - ``q`` -- prime power

    EXAMPLES:

        sage: g = hermitian_form_graph(5,2)
        sage: g.is_distance_regular()
        True

    .. NOTES::
    
        If ``q`` does not satisfy the requirements, then this function
        will raise a ``ValueError``.
      
    TESTS::

    """
    MS = MatrixSpace(GF(q), n, n, implementation="meataxe")
    
    (b,k) = is_prime_power(q, get_data=True)
    if k == 0 or k % 2 != 0:
        raise ValueError("We need q=r^2 where r is a prime power")

    # here we have b^k = q, b is prime and k is even
    r = b**(k//2)
    # so r^2 = b^k = q

    def symmetry(x): return x**r

    hermitianMatrices = MS.symmetric_generator(symmetry)

    rank1Matrices = []
    for mat in hermitianMatrices:
        sig_check()
        if mat.rank() == 1: rank1Matrices.append(mat)

    #refresh generator
    hermitianMatrices = MS.symmetric_generator(symmetry)
    edges = []
    for mat in hermitianMatrices:
        mat.set_immutable()
        for mat2 in rank1Matrices:
            sig_check()

            mat3 = mat + mat2
            mat3.set_immutable()
            edges.append( (mat, mat3) )

    G = Graph(edges, format='list_of_edges')
    G.name("Hermitian form graph on (F_%d)^%d" %(q,n) )
    return G
        
def half_cube( int n ):
    r"""
    Return the graph $\frac 1 2 Q_n$.

    This builds the halved cube graph in ``n`` dimensions.
    The construction is iterative, so the vertices label have no meaning.

    (\lfloor \frac n 2 \rfloor, 1,2, 2 \lceil \frac n 2 \rceil -1)
    
    INPUT:

    - ``n`` -- integer

    EXAMPLES:

        sage: g = half_cube(8) # long time for large n

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

    if n <= 2:
        raise ValueError("we need n > 2")

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

    G.name("Half %d Cube"%n)
    return G        
    


def Grassmann_graph( const int q, const int n, const int input_e ):
    r"""

    Return a Grassmann graph with parameters ``(q,n,e)``.

    This build the Grassmann graph $J_q(n,e)$. That is, for a vector
    space $V = \mathbb F(q))^n$ the output is a graph on the subspaces
    of dimension $e$ where 2 subspaces are adjancent if their intersection
    has dimension $e-1$.

    (e,q,q, gbinom {n-e+1} 1 _q -1)

    INPUT:   
    - ``q`` -- a prime power
    - ``n, e`` -- integers with ``n > e+1``

    EXAMPLES:

        tbd

    TESTS::

        tbd

    """
    if n <= input_e + 1:
        raise ValueError(
            "Impossible parameters n <= e+1 (%d > %d)" %(n,input_e) )
    
    e = input_e
    if n < 2*input_e:
        e = n - input_e
    
    PG = Sage_Designs.ProjectiveGeometryDesign(n-1, e-1, q)
    #we want the intersection graph
    #the size of the intersection must be (q^{e-1} - 1) / (q-1)
    size = (q**(e-1) -  1)/(q-1)
    G = PG.intersection_graph([size])
    G.name("Grassmann graph J_%d(%d,%d)"%(q,n,e))
    return G

def double_Grassmann_graph(const int q, const int e):
    r"""
    vertices : e, e+1 dimensional subsets of (F_q)^(2*e+1)
    edges: (u,v) if u\neq v and (u \in v or v \in u)

    $b_i = (e+1)-c_i$ and $c_{2i} = c_{2i-1} = i$
    """
    
    cdef int n = 2*e+1

    V = VectorSpace(GF(q),n)

    edges = []
    for W in V.subspaces(e+1):
        Wbasis = frozenset(W.basis())
        for U in W.subspaces(e):
            Ubasis = frozenset(U.basis())
            edges.append( ( Wbasis, Ubasis ))
    
    G = Graph(edges,format='list_of_edges')
    G.name("Double Grassmann graph (%d,%d,%d)"%(n,e,q))
    return G

################################################################################
# UNBOUNDED ORDER

def is_hermitian_cover(list arr):
    r"""
    Given an intersection array it return (q,r)
    such that hermitian_cover(q,r) is a graph with the given intersection
    array. If no (q,r) exists, then it returns False
    """
    if len(arr) != 6:
        return False

    k = arr[0] #q^3
    (p,n) = is_prime_power(k,get_data=True)#p^n == k for prime p or n==0
    if n == 0:
        return False

    q = p**(n//3)
    mu = arr[4]#c_2
    r = arr[1]//mu +1

    if r <= 1:#r=1 -> complete graph
        return False

    if arr != [q**3,(r-1)*mu,1,1,mu,q**3]:
        return False

    if (q*q-1)% r != 0:
        return False

    m = (q*q-1)//r
    
    if mu == (q+1)*m:
        #case ii, iii
        if q % 2 == 0 and (q+1)% r == 0:
            #case ii
            return (q,r)
        if q%2 == 1 and ((q+1)//2)%r == 0:
            #case iii
            return (q,r)
        return False
    
    if mu == (q**3 -1)//r and r%2 == 1 and (q-1)%r == 0:
        #case i
        return (q,r)
    
    return False

def hermitian_cover(const int q,const int r):
    r"""
    Implent an antipodal $r$-cover of $K_{q^3+1}$ 
    using the construction due to Cameron ...
    """
    if not is_prime_power(q):
        raise ValueError("invalid input: q must be prime power")

    if not( (r%2 == 1 and (q-1)%r == 0) or
            (q%2 == 0 and (q+1)%r == 0) or
            (q%2 == 1 and ((q+1)//2)%r == 0)):
        raise ValueError("invalid input")

    Fq2 = libgap.GF(q*q)
    one = libgap.One(Fq2)
    zero = libgap.Zero(Fq2)
    gen = libgap.Z(q*q)
    
    #Kgen = gen**r
    # <gen> / <gen^r> = [ gen^i <gen^r> for i in range(r) ]
    #to prove above we have that RHS subset LHS
    #note also any 2 in RHS are distinct
    #so size RHS = size LHS

    #it follows that representatives of Fq2^* / K = [gen^i for i in range(r)]
    Kreps = [ gen**i for i in range(r) ]
    
    #vertices are Kv for isotropic v
    GU = libgap.GU(3,q)
    e1 = [one,zero,zero]
    iso_points = libgap.Orbit(GU,e1,libgap.OnLines)

    vertices = [ k*v for k in Kreps for v in iso_points ]

    #create global variable for function
    libgap.set_global("zero",zero)
    libgap.set_global("r",r)
    libgap.set_global("gen",gen)

    #we need to define the action of GU on (k,v)
    func = """OnKLines := function(v,M)
        local w, i, b, k;

        w := ShallowCopy(v*M);

        i := 1;
        while i < 4 do
            if w[i] <> zero then
                break;
            fi;
            i := i+1;
        od;
        b := w[i];

        i := 1;
        while i < 4 do
             w[i] := w[i]/b;
             i := i+1;
        od;

        k := LogFFE(b,gen);
        i := k mod r;
        b := gen^i;

        return b*w;
    end;"""

    gapOnKLines = libgap.eval(func)
    GUAction = libgap.Action(GU,vertices,gapOnKLines)

    e3 = [zero,zero,one]#other isotropic, with H(e3,e1) = 1 and so e3 ~ e1
    e1pos = libgap.Position(vertices,e1)
    e3pos = libgap.Position(vertices,e3)
    
    #now we have that
    #(e1pos, e11pos) is an edge
    edges = libgap.Orbit(GUAction,[e1pos,e3pos], libgap.OnSets)
    G = Graph(edges, format="list_of_edges")
    return G

def is_AB_graph(list arr):
    r"""
    Returns $n$ s.t. AB_graph(n) has intersection array
    returns False otherwise
    """
    if len(arr) != 6: return False

    twoN = arr[0]+1 #2^n
    (p,n) = is_prime_power(twoN,get_data=True)
    if p != 2: return False

    if n == 1:#we get disconnected graph on 4 vertices
        return False

    if n%2 == 0:#not implemented yet
        return False

    #otherwise we found n
    if arr != [2**n-1,2**n-2,2**(n-1)+1,1,2,2**(n-1)-1]:
        return False
    
    return n

def AB_graph(const int n):
    r"""
    Graph using almost bent function on GF(2)^n
    """

    if n%2 == 0:
        raise ValueError("no knwon AB function for even n")
    
    Fq = GF(2**n)

    f = { x : x**3 for x in Fq }
        
    vectors = [x for x in Fq]

    edges = []
    for i,x in enumerate(vectors):
        for y in vectors[i+1:]:
            for a in vectors:
                sig_check()
                b = a + f[x+y]
                edges.append(( (x,a),(y,b) ))
                edges.append(( (y,a),(x,b) ))

    G = Graph(edges,format="list_of_edges")
    return G

def is_Preparata_graph(list arr):
    r"""
    return (t,i) s.t. Preparata_graph(t,i) has the given
    intersection array.
    """
    if len(arr) != 6: return False
    
    q = (arr[0]+1) // 2
    (p,t) = is_prime_power(q,get_data=True)
    if p!= 2: return False
    if t%2 == 0: return False
    t = (t+1) // 2 #so q = 2^{2t-1}
    #we also have t> 0
    
    p = arr[4]
    (r,i) = is_prime_power(p,get_data=True)
    if r != 2: return False
    i = i-1 #so p = 2^{i+1}
    #we have i >=0

    if i > 2*t-2:
        return False
    
    if arr != [2*q-1,2*q-p,1,1,p,2*q-1]:
        return False

    return (t,i)

def Preparata_graph(const int t,const int i):
    r"""
    Return Preparata graph on $\mathbb F_{2^{2t-1}}$ with subgroup $A$ of size $2^i$

    Inputs: t, i
    """
    
    if i > 2*t-2 or i < 0:
        raise ValueError("i should be between (inclusive) 0 and 2*t-2")

    if t < 1:
        raise ValueError("t should be greater than 1")
    
    q = 2**(2*t-1)
    Fq= GF(q)

    if i != 0:#then A has some meaning
        (Fqvec,fromV,toV) = Fq.vector_space(map=True)
        n = Fqvec.dimension()
        A = []
        for j in range(i):
            v = [0]*n
            v[j] = 1
            v = vector(Fqvec.base_field(), v)
            A.append(v)

        #now A represents a basis for a vector space of dim i
        A = Fqvec.span(A)
        A = [ fromV(x) for x in A]
        #now A is a subgroup of Fq of size 2^i
        Q = set()
        toQ = {}
        Qrep = {}
        for x in Fq:
            sig_check()
            xA = frozenset( [x+a for a in A])
            toQ[x] = xA
            Qrep[xA] = x
        for k in Qrep:
            Q.add(Qrep[k])
            
    else:
        Q = Fq
        
    edges  = []
    for x in Fq:
        x2 = x*x
        x3 = x2*x
        for y in Fq:
            y2 = y*y
            r = x2*y+x*y2
            x3py3 = x3+y2*y
            for a in Q:
                sig_check()
                if x != y or r != 0:
                    b = r+a
                    if i != 0: b = Qrep[toQ[b]]
                    edges.append(( (x,0,a),(y,0,b) ))
                    edges.append(( (x,1,a),(y,1,b) ))
                b = r + x3py3 +a
                if i != 0: b = Qrep[toQ[b]]
                edges.append(( (x,0,a),(y,1,b) ))
                edges.append(( (x,1,a),(y,0,b) ))

    G = Graph(edges, format="list_of_edges")
    G.name("Preparata graph on 2^(2%d-1)"%t)
    return G

def is_Brouwer_Pasechnik_graph(list arr):
    r"""
    returns q s.t. Brouwer_Pasechnik_graph(q)
    has the intersection array passed;
    returns False if q doesn't exists
    """
    if len(arr) != 6: return False
    q = arr[4]
    if not is_prime_power(q):
        return False
    if arr != [q**3-1,q**3-q,q**3-q**2+1,1,q,q**2-1]:
        return False
    return q

def Brouwer_Pasechnik_graph(const int q):

    Fq = GF(q)

    def cross(v,w):
        z = [ v[1]*w[2]-v[2]*w[1], v[2]*w[0]-v[0]*w[2], v[0]*w[1]-v[1]*w[0] ]
        return vector(Fq,z)
            
    V = list(VectorSpace(Fq,3))
    for v in V:
        v.set_immutable()

    edges = []
    for u in V:
        for v in V:
            for v2 in V:
                sig_check()
                if v2 == v: continue #otherwise cross(v,v2) == 0 and u2 == u
                u2 = u+ cross(v,v2)
                u2.set_immutable()
                edges.append(( (u,v),(u2,v2) ))

    G = Graph(edges,format="list_of_edges")
    G.name("Brouwer-Pasechnik graph on GF(%d)"%q)
    return G

def is_Pasechnik_graph(list arr):
    r"""
    Returns q s.t. Pasechnik_graph(q) has the intersection array
    given; returns False if q doesn't exists
    """
    if len(arr) != 8: return False
    q = arr[5]
    if not is_prime_power(q):
        return False
    if arr != [q**3,q**3-1,q**3-q,q**3-q**2+1,1,q,q**2-1, q**3]:
        return False
    return q

def Pasechnik_graph(const int q):
    H = Brouwer_Pasechnik_graph(q)
    G = extended_biparitite_double_graph(H)
    G.name("Pasechnik graph on D_4(%d)"%q)
    return G

def is_from_association_scheme(list arr):
    r"""
    Return (n,r) if graph_from_association_scheme(n,r) has the given intersection array
    It returns False if this is not the case
    """
    if len(arr) != 6: return False
    n = arr[0]
    mu = arr[4]
    
    if n<= 0 or  mu <= 0 or (n-1)%mu != 0: return False
    r = (n-1) // mu
    
    if r == 1:#complete graph
        return False
    if arr != [n,(r-1)*mu,1,1,mu,n]:#this is any r cover of K_{n+1}
        return False
    if distance_regular_association_scheme(n,r,existence=True) is not True:
        return False
    return (n,r)

def graph_from_association_scheme(const int n, const int r):
    S = distance_regular_association_scheme(n,r,check=False)
    inf = "inf" if "inf" not in S.ground_set() else Integer(S.num_points())
    while inf in S.ground_set(): #this makes sure that inf not in S
        inf += 1
        
    return association_scheme_graph(S,inf)

def association_scheme_graph(scheme, inf = "inf"):
    r"""
    Return the graph related to the given association scheme.

    We need inf not to be a point of the scheme
    """
    if inf in scheme.ground_set():
        raise ValueError("inf must not be in the association scheme")

    r = scheme.num_classes()
    X = scheme.ground_set()
    I = list(range(1,r+1))

    edges = []
    for x in X:
        for i in I:
            edges.append(( (inf,i),(x,i) ))

    n = scheme.num_points()
    for x in range(n):
        for y in range(x+1,n):
            ij = scheme.matrix()[x][y]
            for i in I:
                j = (ij -i)%r
                if j == 0: j = r
                edges.append(( (X[x],i),(X[y],j) ))
                edges.append(( (X[y],i),(X[x],j) ))
    
    G = Graph(edges,format="list_of_edges")
    return G

def is_from_GQ_spread(list arr):
    r"""
    Returns (s,t) s.t. the graph obtained from a GQ of order (s,t) with a spread
    has the correct intersection array
    """
    if len(arr) != 6: return False
    t = arr[4]+1
    
    if t <= 1: return False
    
    s = arr[1] // (t-1)
    
    if arr != [s*t,s*(t-1),1,1,t-1,s*t]:
        return False
    
    if s == 1 and t == 1:#in this case we don't get a connected graph
        return False

    if generalised_quadrangle_with_spread(s,t,existence=True) is not True:
        return False
    
    return (s,t)

def graph_from_GQ_spread(const int s,const int t):
    (GQ,S) = generalised_quadrangle_with_spread(s,t,check=False)
    return GQ_spread_graph(GQ,S)

def GQ_spread_graph(GQ, S):
    r"""
    Point graph of the generalised quadrangle GQ without its spread S
    """
    k = len(GQ.blocks()[0])
    edges = []
    for b in GQ.blocks():
        if b in S: continue
        for i in range(k):
            p1 = b[i]
            for j in range(i+1,k):
                sig_check()
                p2 = b[j]
                edges.append( (p1,p2) )

    G = Graph(edges, format="list_of_edges")
    return G

def is_symplectic_cover(list arr):
    r"""
    Returns (q,n,r) s.t. symplectic_cover(q,n,r)
    has the intersection array given. It returns False otherwise.
    """

    if len(arr) != 6: return False
    
    qn = arr[0]+1

    if arr[4] == 0:
        return False
    
    r = qn // arr[4]

    if r <= 1: return False
    if arr != [qn-1,((r-1)*qn)//r,1,1,qn//r,qn-1]:
        return False
    
    (p,k) = is_prime_power(qn,get_data=True)
    if k == 0:
        return False #q not a prime power
    #q^n = p^k

    #n even -> k even
    if k%2 == 1: return False
    if qn%r != 0: return False 
    (p,j) = is_prime_power(r,get_data=True)

    #q = p^i for i>= j (so r|q) and n(=k/i) even
    for i in range(j,k//2+1):
        if k%i == 0 and (k//i)%2 == 0:
            q = p**i
            n = k//i
            break
            #q^n = p^k; r = p^j | p^i since i >= j
    else:
        #we found no suitable q
        return False
    
    return (q,n,r)

def symplectic_cover(const int q, const int n, const int r):
    r"""
    Returns an r-antipodal cover of $K_{q^n}$ using a symplectic form over $\mathbb F_q$
    with a subgroup of index r
    """
    if n <= 0:
        raise ValueError("n must be positive")
    if n%2 == 1:
        raise ValueError("n must be even")
    if q%r != 0:
        raise ValueError("r must be a factor of q")

    def ei(i,m):
        v = [0]*m
        v[i] = 1
        return v

    Fq = GF(q)
    V = VectorSpace(Fq,n)

    if r != q:
        #we need A to be a subgroup of the additive group of Fq
        #so we make Fq a vectorspace and A is a subspace
        (Fqvec,fromVec,toVec) = Fq.vector_space(map=True)
        (p,k) = is_prime_power(r,get_data=True)
        Adim = Fqvec.dimension() -k #|A| = q / r 
        A = Fqvec.span([ei(i,Fqvec.dimension()) for i in range(Adim)])
        A = [ fromVec(x) for x in A ]

        Q = set()
        toQ = {}# map a -> a+A
        Qrep = {}#map a+A -> a (pick unique representative for each a+A)
        for x in Fq:
            sig_check()
            xA = frozenset([x+a for a in A])
            Q.add(xA)
            toQ[x] = xA
            Qrep[xA] = x
        Q = set([ Qrep[xA] for xA in Q])

    else:
        Q = Fq

    
    #symplectic form has matrix
    #  0 I
    # -I 0
    M = []
    n2 = n//2
    for i in range(n):
        sig_check()
        row = [0]*n
        if i < n2:
            row[n2+i] = 1
        else:
            row[i-n2] = -1
        M.append(row)
    M = Matrix(Fq,M)


    vectors = list(V)
    for v in vectors:
        v.set_immutable()

    edges = []
    k = len(vectors)
    for i in range(k):
        x = vectors[i]
        for j in range(i+1,k):
            y = vectors[j]
            Bxy = x*M*y
            Byx = - Bxy
            for b in Q:
                sig_check()
                a = b + Bxy
                a2 = b + Byx
                if r != q:
                    a = Qrep[toQ[a]]
                    a2 = Qrep[toQ[a2]]
                   
                edges.append( ( (a,x),(b,y) ) )
                edges.append( ( (a2,y),(b,x) ) )

    G = Graph(edges, format="list_of_edges")
    G.name("Symplectic antipodal %d cover of K_{%d^%d}"%(r,q,n))#to be changed
    return G

def is_from_square_BIBD(list arr):
    r"""
    Returns (v,k) s.t. graph_from_BIBD(v,k) has the correct
    intersection array; False otherwise
    """
    if len(arr) != 6: return False
    k = arr[0]
    l = arr[4]
    if l == 0 or (k*(k-1))%l != 0: return False
    v = (k*(k-1))//l +1
    
    if k <= 2: return False #trivial cases
    if v == k: return False #diameter 2
    #this will force v >= 4 as there is no BIBD with v<k
    
    if arr != [k, k-1, k-l, 1,l,k]:
        return False

    if Sage_Designs.balanced_incomplete_block_design(v,k,lmbd=l,existence=True) is not True:
        return False

    return (v,k)

def graph_from_square_BIBD(const int v,const int k):
    if v == 1 or (k*(k-1))%(v-1) != 0:
        raise ValueError("no square BIBD exists with v={}, k={}".format(v,k))
    lmbd = (k*(k-1))//(v-1)
    D = Sage_Designs.balanced_incomplete_block_design(v,k,lmbd=lmbd)
    return D.incidence_graph()

def is_from_Denniston_arc(list arr):
    r"""
    Return n s.t. graph_from_Denniston_arc(n) has the given intersection array.
    Return False if such n doesn't exists.
    """
    if len(arr) != 8: return False
    n = arr[3]
    (p,k) = is_prime_power(n,get_data=True)
    if p != 2: return False

    if arr != [n*n-n+1,n*(n-1),n*(n-1),n,1,1,(n-1)**2,n*n-n+1]:
        return False
    return n

def graph_from_Denniston_arc(const int n):
    r"""
    Returns the distance regular graph related to the Denniston n-arc on $\mathbb F_{n^2}$
    """
    (p,k) = is_prime_power(n,get_data=True)
    if p != 2:
        raise ValueError("input must be a power of 2")
    
    q = n*n
    Fq = GF(q)
    Fn = GF(n)
    elemsFq = [ x for x in Fq]

    #ensure elemsFq[0] == 0
    if not elemsFq[0].is_zero():
        for i,x in enumerate(elemsFq):
            sig_check()
            if x.is_zero():
                y = elemsFq[0]
                elemsFq[0] = x
                elemsFq[i] = y
                break

    #find irreducible quadratic
    candidates = set(Fq)
    for x in elemsFq[1:]:#we rely on the first element to be 0
        sig_check()
        a = x + (1/x)
        candidates = candidates.difference({a})

    irrCoef = candidates.pop()
    def Q(x,y):
        return x*x+irrCoef*x*y+y*y

    PG = Sage_Designs.ProjectiveGeometryDesign(2,1,q) #projective plane PG(2,q)
    #the points are represented as vectors with homogenous coordinates (first non-zero entry is 1)

    arc = set() #complete arc
    for x in elemsFq:
        for y in elemsFq:
            sig_check()
            if Q(x,y) in Fn:
                arc.add(vector(Fq,[1,x,y],immutable=True))

    #pick all lines intersecting arc in n points (so any line intersecting the arc)
    #remove all points in arc
    lines = []
    for b in PG.blocks():
        sb = Set(b)
        for p in b:
            sig_check()
            if p in arc:
                newLine = sb.difference(arc)
                lines.append(newLine)
                break

    #now we have a list of all lines of the complement
    edges = []
    for b in lines:
        bs = frozenset(b)
        for p in b:
            sig_check()
            edges.append( (p,bs) )

    G = Graph(edges,format="list_of_edges")
    G.name("Incidence graph of the complement of a complete %d-arc in PG(2,%d)"%(n,q))
    return G

def is_unitary_nonisotropic_graph(list arr):
    r"""
    Return q s.t. unitary_nonisotropic_graph(q) has the intersection array given.
    Return False otherwise.
    """
    if len(arr) != 6: return False
    q = arr[2]-1
    if not is_prime_power(q):
        return False
    if q <= 2: return False

    if arr != [q*q-q,q*q-q-2,q+1,1,1,q*q-2*q]:
        return False
    return q

def unitary_nonisotropic_graph(const int q):
    r"""
    Return graph on nonisotropic points for a Hermitian form on $(\mathbb F_{q^2})^3$
    """
    if q < 3:
        raise ValueError("q must be greater than 2")
    if not is_prime_power(q):
        raise ValueError("q must be a prime power")


    GU = libgap.GU(3,q)
    Fr = libgap.GF(q*q)
    one = libgap.One(Fr)
    zero = libgap.Zero(Fr)
    ev = [one,one,zero]
    w = [zero,one,-one]

    vertices = libgap.Orbit(GU,ev,libgap.OnLines)
    PGU = libgap.Action(GU,vertices,libgap.OnLines)

    evPos = -1
    wPos = -1
    for i,v in enumerate(vertices):
        if v == ev:
            evPos = i+1
        if v == w:
            wPos = i+1

        if evPos != -1 and wPos != -1:
            break

    edges = libgap.Orbit(PGU, libgap.Set([evPos,wPos]), libgap.OnSets)

    G = Graph(edges,format="list_of_edges")
    G.name("Unitary nonisotropic graph on (F_%d)^3"%(q*q))
    return G

def is_Taylor_graph(list arr):
    r"""
    Return (n,l) s.t. Taylor_graph(n,l) has the intersection array give.
    Return False otherwise
    """
    if len(arr) != 6: return False
    k = arr[0]
    mu = arr[1]
    if k == 0 or mu == 0:
        return False
    if arr != [k,mu,1,1,mu,k]:
        return False
    
    n = k+1
    if n < 3: return False#no block

    
    #two-graph has $n$ points
    l = k - mu-1 #any 2 points are in a_1 triangles
    #hence any 2 points are in l blocks

    if l == n-2:#complete two-graph -> graph is disconnected
        return False

    if two_graph(n,l,regular=True,existence=True) is not True:
        return False
    return (n,l)

def Taylor_graph(const int n,const int l):
    D = two_graph(n,l,regular=True,check=False)
    G = graph_from_two_graph(D)
    return G

def graph_from_two_graph( D ):
    r"""
    Given a two graph (block design) it builds the graph associated with it.
    """

    edges = []
    
    #vertices = x^+, x^- for all x\in X
    # x^a,y^b are adjecent if: x != y and ( (a == b and {x,y,inf} coherent) or ( a != b and {x,y,inf} not coherent) )
    # inf is just a point in X
    inf = D.ground_set()[0]

    #first we do all coherent edges
    S = set() #set of coherent pairs
    for b in D.blocks():
        sig_check()
        if b[0] == inf: x=b[1]; y=b[2]
        elif b[1] == inf: x=b[0]; y=b[2]
        elif b[2] == inf: x=b[0]; y=b[1]
        else: continue
        #now x,y,inf are coherent
        S.add( frozenset([x,y]) )
        edges.append( ((x,0),(y,0)) )
        edges.append( ((x,1),(y,1)) )

    #inf is coherent with any other vertex!
    for x in D.ground_set()[1:]:#we don't want edge inf inf
        sig_check()
        #{x,inf,inf} is coherent
        edges.append( ((x,0),(inf,0)) )
        edges.append( ((x,1),(inf,1)) )
        S.add( frozenset([x,inf]) )

    #now we can handle the non-coherent ones
    l = D.num_points()
    for i in range(l):
        x = D.ground_set()[i]
        for j in range(i+1,l):#go through all ordered pairt
            sig_check()
            y = D.ground_set()[j]
            if frozenset([x,y]) in S: continue#x,y,inf coherent
            #otherwise add edge
            edges.append( ((x,0),(y,1)) )
            edges.append( ((x,1),(y,0)) )

    G = Graph(edges,format="list_of_edges")
    return G

def is_from_TD(list arr):
    r"""
    Return (m,u) s.t. graph_from_TD(m,u) has the intersection array given.
    Return False if (m,u) don't exist.
    """
    if len(arr) != 8: return False

    u = arr[5]
    if u == 0 or arr[0]%u != 0: return False
    m = arr[0]//u

    if m == 1: return False #graph is srg
    if arr!=[m*u,m*u-1,(m-1)*u,1,1,u,m*u-1,m*u]:
        return False

    if Sage_Designs.symmetric_net(m,u,existence=True) is not True:
        return False
    
    return (m,u)

def graph_from_TD(const int m, const int u):
    r"""
    Return the incidence graph of a symmetric tansversal design with parameters m,u.
    """
    SN = Sage_Designs.symmetric_net(m,u)
    return SN.incidence_graph()


def generalised_dodecagon(const int s, const int t):
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
        lines = extract_lines(H)
        points = list(H.vertices())

        edges = []
        for p in points:
            for l in lines:
                sig_check()
                if p in l:
                    edges.append( (p,l) )

        G = Graph(edges, format='list_of_edges')
        G.name("Generalised dodecagon of order (1,%d)"%q)
        return G
    
    else: #orderType == 1
        #dual
        H = generalised_dodecagon(t,s)
        G = line_graph_generalised_polygon(H)
        G.name("Generalised dodecagon of order (%s,%d)"%(s,t))
        return G

def generalised_octagon(const int s, const int t):
    cdef int q = 0
    cdef int orderType = 0
    if s == 1:# (1,q)
        q = t
    elif t == 1:# (q,1)
        q = s
        orderType = 1
    elif s**2 ==  t:# (q,q^2)
        q = s
        (p,k) = is_prime_power(q,get_data=True)
        if p != 2 or k%2 != 1:
            raise ValueError("generalised octagon (q,q^2) only for q odd powers of 2")
        orderType = 2
    elif t**2 == s: #(q^2,q)
        q = t
        orderType = 1
    else:
        raise ValueError("invalid input")

    if not is_prime_power(q):
        raise ValueError("invalid input")

    if orderType == 0:
        H = strongly_regular_graph((q+1)*(q*q+1),q*(q+1),q-1,q+1,check=False)
        # above is pointgraph of generalised quadrangle (q,q)
        lines = extract_lines(H)
        points = list(H.vertices())
        #points and lines make the quadrangle

        edges = []
        for p in points:
            for l in lines:
                sig_check()
                if p in l:
                    edges.append( (p,l) )

        G = Graph(edges, format='list_of_edges')
        G.name("Generalised octagon of order (1,%d)"%q)
        return G
        
    elif orderType == 1:
        #dual
        H = generalised_octagon(t,s)
        G = line_graph_generalised_polygon(H)
        G.name("Generalised octagon of order(%d,%d)"%(s,t))
        return G
    else:
        if q == 2:
            g = libgap.AtlasGroup("2F4(2)", libgap.NrMovedPoints, 1755)
            G = Graph( g.Orbit( [1,73], libgap.OnSets), format='list_of_edges')
            G.name("Generalised octagon of order (2,4)")
            return G
        else:
            raise NotImplementedError("graph would be too big")
    pass
    
def extract_lines( G ):
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

    lines = []
    edges = set(G.edges(labels=False,sort=False))

    while edges :
        (x,y) = edges.pop()

        #compute line
        bottomX = set(G.neighbors(x,closed=True))
        bottomY = set(G.neighbors(y,closed=True))
        bottom1 = bottomX.intersection(bottomY)

        b = bottom1.pop()
        bottom2 = frozenset(G.neighbors(b,closed=True))
        for v in bottom1:
            sig_check()
            s = frozenset(G.neighbors(v,closed=True))
            bottom2 = bottom2.intersection(s)

        #now bottom2 is a line
        lines.append(tuple(bottom2))#we need tuple or GAP will complain
        
        #remove pointless edges†
        for u in bottom2:
            for v in bottom2:
                try :
                    edges.remove( (u,v) )
                except KeyError:
                    pass #ignore this
                
    #end while edges

    return lines

def line_graph_generalised_polygon(H):
    lines = extract_lines(H)

    #get a map point -> all lines incident to point
    vToLines = { v : [] for v in H.vertices(sort=False) }
    for l in lines:
        for p in l:
            sig_check()
            vToLines[p].append(l)

    k = len(vToLines[lines[0][0]])

    edges = []
    for v in vToLines:
        lines = vToLines[v]
        for i,l in enumerate(lines):
            for j in range(i+1,k):
                sig_check()
                edges.append( (l,lines[j]) )
    
    G = Graph(edges,format="list_of_edges")
    return G

def generalised_hexagon( const int s, const int t):
    r"""
    to use libgap.AtlasGroup we need to do
    sage -i gap_packages
    """
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
        PG2 = Sage_Designs.ProjectiveGeometryDesign(2,1,q)

        edges = []
        for l in PG2.blocks():
            for p in l:
                sig_check()
                edges.append( (p, frozenset(l)) )
                    
        G = Graph(edges, format='list_of_edges')
        G.name("Generalised hexagon of order (1,%d)"%q)
        return G
    
    elif orderType == 1:
        # "dual" graph 
        H = generalised_hexagon(t,s)
        G = line_graph_generalised_polygon(H)
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
        elif q <= 5:
            arr = intersection_array_2d_gon(3,s,t)
            n = number_of_vertices_from_intersection_array(arr)
            G = graph_from_permutation_group( libgap.AtlasGroup("G2(%d)"%q, libgap.NrMovedPoints, n), arr[0])
            G.name("Generalised hexagon of order (%d,%d)"%(q,q))
            return G
        else:
            raise NotImplementedError("graph would be too big")
        
    elif orderType == 3:
        if q> 3: raise ValueError("graph would be too big")
        movedPoints = 819 if q==2 else 26572
        group = libgap.AtlasGroup("3D4(%d)"%q,libgap.NrMovedPoints,movedPoints)
        G = Graph(group.Orbit([1,2],libgap.OnSets), format='list_of_edges')
        G.name("Generalised hexagon of order (%d,%d)"%(q,q**3))
        return G
    pass


def graph_from_permutation_group( group, const int order ):
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

def is_from_Kasami_code(list arr):
    if len(arr) != 6: return False
    q = arr[4]
    (p,k) = is_prime_power(q,get_data=True)
    if p != 2: return False

    if arr == [q*q-1,q*q-q,1,1,q,q*q-1]:
        return (q*q,q)

    qk = arr[0]+1
    n = 1
    qn = q
    while qn < qk:
        qn *= q
        n += 1
    #here either qn = qk and so q^n = qk
    #or qn > qk and so qk is not a powe of q
    if qn > qk: return False
    if n%2 == 0: return False
    j = (n-1) //2
    if j== 0: return False
    
    assert(qn == q**(2*j+1), "The code is incorrect")

    if arr == [qn-1,qn-q,q**(2*j)*(q-1)+1,1,q,q**(2*j)-1]:
        return (qn,q)

    return False

def Kasami_graph(const int s, const int t):
    K = Kasami_code(s,t)
    G = coset_graph(2,K.basis(),n=s-1)
    G.name("Coset graph of Kasami code (%d,%d)"%(s,t))
    return G

def is_from_extended_Kasami_code(list arr):
    if len(arr) != 8: return False
    q = arr[5]
    (p,k) = is_prime_power(q,get_data=True)
    if p != 2: return False

    if arr == [q*q, q*q-1, q*q-q,1,1,q,q*q-1,q*q]:
        return (q*q,q)

    qk = arr[0]
    n=1
    qn = q
    while qn < qk:
        n += 1
        qn *= q
    if qn > qk: return False
    if n%2 == 0: return False
    j = (n-1)//2
    if j== 0: return False

    assert(qn == q**(2*j+1), "Something is badly wrong")
    
    if arr == [qn,qn-1,qn-q,q**(2*j)*(q-1)+1,1,q,q**(2*j)-1,qn]:
        return (qn,q)

    return False

def extended_Kasami_graph(const int s, const int t):
    K = extended_Kasami_code(s,t)
    G = coset_graph(2,K.basis(), n=s)
    G.name("Coset graph of extended Kasami code (%d,%d)"%(s,t))
    return G


################################################################################
# UTIL FUNCTIONS

def number_of_vertices_from_intersection_array( array ):
    r"""
    if array is not a valid intersection array, then errors are likely to occur
    """
    n = len(array)
    if n%2 == 1:
        raise ValueError("intersection array must have even length")

    if 0 in array:
        raise ValueError("intersection array must be positive")
    
    cdef int d = len(array) // 2

    cdef int ki = 1
    cdef int v = 1
    # invariant v = sum([k_0,..,k_i))
    for i in range(1,d+1):
        ki = (ki*array[i-1]) // array[d+i-1] # k_{i+1} = k_i*b_i /c_{i+1}
        v += ki

    return v

# from bouwer book, we assume d \gt 3 [not sure if it works with smaller d]
def intersection_array_from_classical_parameters( const int d,
                                                  const int b,
                                                  alpha_in,
                                                  beta_in ):
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
    if d < 3:
        raise ValueError("we only deal with diameter > 2")

    beta = Rational(beta_in)
    alpha = Rational(alpha_in)
    if beta.is_integer(): beta = int(beta)
    if alpha.is_integer(): alpha = int(alpha)
    
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
    if t is False:
        raise ValueError("the graph passed is not distance_regular")
    (b,c) = t
    # annoyingly b ends with None (b_d = 0)
    # and c starts with None (c_0 = 0)
    # so trim these 2 values
    return b[:-1]+c[1:]
    
def is_classical_parameters_graph(list array):
    r"""
    checks if Sage can build a graph for the given parameters;
    if so returns an integer gamma s.t. graph_with_classical_parameters(d,b,alpa,beta,gamma)
    returns the given graph.
    The value of gamma is used for internal purpose only;
    If this is not the case it returns False
    """
    import drg
    from sage.functions.log import log
    from sage.rings.integer_ring import ZZ

    def integral_log(const int x, const int b):
        #compute log_b(x) if is not a positive iteger, return -1
        if x <= 0: return -1
        k = log(x,b)
        if k in ZZ and k > 0:
            return int(k)
        return -1
        
    #compute the classical parameters
    #then find out which graph we have
    #gamma is simply an integer indicating the type of graph

    #gamma -> graph
    #  0   -> Johnson
    #  1   -> Hamming
    #  2   -> Halved cube
    #  3   -> UnitaryDualPolarGraph 2d, -b
    #  4   -> hermitian form
    #  5   -> gen hexagon
    #  6   -> Grassmann
    #  7   -> Dual Polar Orthogonal e=1
    #  8   -> Dual Polar symplectic
    #  9   -> Dual Polar Orthogonal e=-1
    # 10   -> Unitary dual polar 2d+1
    # 11   -> Unitary dual polar 2d
    # 12   -> Ustimenko
    # 13   -> Bilinear form graph
    # 14   -> Alternating form graph
    
    # b_i = arr[i]; c_i = arr[d - 1 + i]
    if len(array) % 2 != 0 : return False
    d = len(array) // 2

    #this may fail is array is very bad
    #however, we did check in distance_regular_graph
    #so it should not happen
    p = drg.DRGParameters(array[:d],array[d:])
    t = p.is_classical()
    
    if t is False:
        return False

    (d,b,alpha,beta) = t[0]
    gamma = None
    
    if b == 1 :
        if alpha == 1 and beta >= d:#since beta+d = n >= 2*d
            # Johnson Graph
            gamma = 0
        elif alpha == 0:
            # Hamming Graph
            gamma = 1
        elif alpha == 2 and ( beta == 2*d + 1 or beta == 2*d -1):
            # Halved cube graph
            gamma = 2
        else :
            return False
    elif b < 0 and is_prime_power(-b):
        if alpha +1 == (1 + b*b)/(1 + b) and beta +1 == (1-b**(d+1))/(1+b):
            # U(2d,r)
            gamma = 3
        elif alpha + 1 == b and beta + 1 == - (b**d):
            gamma = 4
        elif d == 3 and alpha + 1 == 1 / (1+b) and beta + 1 == q_binomial(3,1,-b):
            q = -b
            if q < 4:
                gamma = 5
            else:#too big
                return False
        else:
            return False

    if gamma is not None:
        return (d,b,alpha,beta,gamma)

    #all remaining cases need b to be a prime power
    (p,k) = is_prime_power(b,get_data=True)
    if k == 0: return False#b not a prime power
    r = p**(k//2) #will be used later

    if alpha == b and integral_log( (beta +1)*(b-1)+1, b ) >= d+1:
        # we checked that beta + 1 = (b^(n-d+1) - 1)/(b - 1) for n >= 2d
        # Grassmann graph
        gamma = 6
    elif alpha == 0 and  beta*beta in {1, b, b*b, b**3, b**4}:
        #checked beta in {b^0, b^(0.5), b, b^(1.5), b^2}
        # dual polar graphs
        if beta == 1:
            #maximal Witt index
            gamma = 7
        elif beta == b:
            #dual sympletic
            gamma = 8
        elif beta == b*b:
            #non maximal Witt index
            gamma = 9
        else:
            if k%2 == 1: return False#we need b a square
            if beta == r**3:
                #hermitian form
                gamma = 10
            elif beta == r:
                #other hermitian form
                gamma = 11
    elif ( k%2 == 0 and alpha + 1 == q_binomial(3, 1, r)
           and beta + 1 in { q_binomial(2*d+2, 1, r),
                             q_binomial(2*d+1, 1, r) }
    ):
        # Ustimenko
        gamma = 12    
    elif alpha + 1 == b and integral_log( beta+1, b) >= d:
        gamma = 13
    elif (k%2 == 0 and alpha + 1 == b
          and beta + 1 in { r**(2*d-1),r**(2*d+1) }
    ):
        gamma = 14

    if gamma is None: return False
    return (d,b,alpha,beta,gamma)

def graph_with_classical_parameters(const int d, const int b, alpha_in, beta_in, const int gamma):
    from sage.functions.log import log
    from sage.functions.other import sqrt

    alpha = Rational(alpha_in)
    beta = Rational(beta_in)
    if alpha.is_integer(): alpha = int(alpha)
    if beta.is_integer(): beta = int(beta)

    if gamma == 0:
        return GraphGenerators.JohnsonGraph(beta+d,d)
    elif gamma == 1:
        return GraphGenerators.HammingGraph(d,beta+1)
    elif gamma == 2:
        a = 0 if beta == 2*d+1 else 1
        return half_cube(beta + a)
    elif gamma == 3:
        return GraphGenerators.UnitaryDualPolarGraph(2*d,-b)
    elif gamma == 4:
        return hermitian_form_graph(d,(-b)**2)
    elif gamma == 5:
        q = -b
        return generalised_hexagon(q,q**3)
    elif gamma == 6:
        n = int(log( (beta+1)*(b-1)+1, b)) + d -1
        return Grassmann_graph(b,n,d)
    elif gamma == 7:
        return dual_polar_orthogonal(1,d,b)
    elif gamma == 8:
        return GraphGenerators.SymplecticDualPolarGraph(2*d,b)
    elif gamma == 9:
        return dual_polar_orthogonal(-1,d,b)
    elif gamma == 10:
        r = int(sqrt(b))
        return GraphGenerators.UnitaryDualPolarGraph(2*d+1,r)
    elif gamma == 11:
        r = int(sqrt(b))
        return GraphGenerators.UnitaryDualPolarGraph(2*d,r)
    elif gamma == 12:
        q = int(sqrt(b))
        m = int(log( (beta+1)*(q-1)+1, q)) -1
        Ustimenko_graph(m,q)
    elif gamma == 13:
        e = int(log(beta+1,b))
        return bilinear_form_graph(d,e,b)
    elif gamma == 14:
        q = int(sqrt(b))
        a = 0 if beta+1 == q**(2*d-1) else 1
        return alternating_form_graph(2*d+a,q)

    raise ValueError("incorrect value of gamma")

def intersection_array_of_pseudo_partition_graph(m,a):
    r"""
    Return intersection array of pseudo partiotion graph with parameters m,a

    m = 2*d or 2*d +1
    b_i = (m-i)(1 + a(m-1-i)) for i < d
    c_i = i(1+ a(i-1)) for i < d
    b_d = 0; c_d = g*d(1+a(d-1)) where g =2 - m % 2
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
    if the array is no good, then returns False
    p197

    we only handle d >= 3
   

    """
    d = len(arr)
    if d % 2 != 0:
        return False

    d = d // 2

    if d < 3 :
        return False
    
    #m = 2*d or 2*d +1
    #b_i = (m-i)(1 + a(m-1-i)) for i < d
    #c_i = i(1+ a(i-1)) for i < d
    #b_d = 0; c_d = g*d(1+a(d-1)) where g = 2- m % 2

    #c_2 = 2 ( 1+a)
    c2 = arr[d+1]
    if c2 % 2 != 0:
        return False
    a = c2 // 2 -1

    if a not in {0,1,2}:#we don't know these graphs
        return False

    cd = arr[2*d-1]
    K = d*(1+a*(d-1))
    if cd%K != 0:
        return False
    gamma = cd //K

    if gamma == 2:
        m = 2*d
    elif gamma == 1:
        m = 2*d+1
    else:
        return False

    newArr = intersection_array_of_pseudo_partition_graph(m,a)
    if arr == newArr:
        return (m,a)

    return False

def is_near_polygon(list arr):
    r"""
    Checks if the intersection array could be of a near polygon. if so returns a parameter l, otherwise -1

    p199 theorem 6.4.1:
    a dist-reg graph with int. arr [b_0,...,b_{d-1}, c_1, ..., c_d] is a regular near polygon
    iff there is no induced subgraph K_{1,1,2} and there is l s.t. b_i = k - (l+1)*c_i for i = 0,..,d-1.

    In particular, if it is a near polygon, then is a near 2d-gon if k = (l+1)*c_d and a near (2d+1)-gon otherwise
    """
    def is_generalised_2d_gon(a,d):
        #c_1,...,c_{d-1} = 1
        for i in range(1,d):
            if a[d+i-1] != 1: return False

        t = a[2*d-1] -1 #c_d-1
        
        # b_0 = s(t+1)
        if a[0] % (t+1) != 0: return False
        s = a[0] // (t+1)

        if not is_prime_power(s*t):#this also rules out (1,1)
            return False
       
        if d == 3:
            if s == 1 or t == 1:
                #order (1,q) or (q,1)
                return True
            elif s == t and s in {2,3,4,5}:
                #order (q,q)
                return True
            elif (s==t**3 or t == s**3) and s*t in {16,81}:
                #order (q,q^3) or (q^3,q); q is 2 or 3
                return True
            return False
        elif d == 4:
            if s== 1 or t == 1:
                #order (1,q) or (q,1)
                q= s*t
                if strongly_regular_graph((q+1)*(q*q+1),q*(q+1),q-1,q+1,existence=True):
                    return True
            elif s==t*t or s*s == t and s*t == 8:
                #order (q,q^2) we can only do q=2
                return True
            return False
        elif d == 6:
            if (s==1 or t == 1) and s*t in {2,3,4,5}:
                #order (1,q); rely on hexagon (q,q)
                return True
        
        return False

    #gamma indicates what graph we have
    # gamma -> graph
    #   0   -> gen polygon
    #   1   -> polygon
    #   2   -> Odd graph
    #   3   -> 2xGrassmann
    #   4   -> 2xodd
    #   5   -> folded cube

    d = len(arr)
    if d % 2 != 0:
        return False

    d = d // 2
    if d < 3:
        return False
    
    k = arr[0]
    l = k - arr[1] - 1#b_i = k -(\l+1)
    if l < 0: return False
    
    #for i = 0 we have b_0 = k - (l+1)*c_0 = k since c_0 = 0 always
    for i in range(1,d):
        if arr[i] != k - (l+1)*arr[d+i-1]: #b_i = k - (l+1)c_i
            return False

    #chek k >= (l+1)c_d
    if k < (l+1)*arr[2*d-1]:
        return False

    #now find if we can build this graph
    n = 2*d if k == (l+1)*arr[2*d-1] else 2*d+1
    cs = arr[d:]
    
    #is generalised polygon?
    if is_generalised_2d_gon(arr,d):
        t = arr[2*d-1]-1
        s = arr[0]//(t+1)
        return (0,(d,s,t))
    
    if l != 0: return False#classial parameters; don't deal it here

    #now l==0
    if k== 2 and cs == ([1 for i in range(1,d)]+[2*d+2-n]):
        #polygon
        return (1,n)

    if n == 2*d+1 and k == d+1 and cs == [(i+1)//2 for i in range(1,d+1)]:
        #odd graph
        return (2,d+1)

    if ( n == 2*d and d%2 == 1 and is_prime_power(cs[2]-1) and
         k == q_binomial((d-1)//2+1, 1,cs[2]-1) and#cs[2]=c_3 = q_binom(2,1,q) = q+1
         cs == [ q_binomial((i+1)//2,1,cs[2]-1) for i in range(1,d+1)]):
        #double grassman
        e = (d-1)//2
        q = cs[2]-1
        return (3,(q,e))

    if ( n==2*d and d%2 == 1 and k -1 == (d-1)//2 and
         cs == [(i+1)//2 for i in range(1,d+1)] ):
        #doubled odd
        e = (d-1)//2
        return (4,e)
    
    if k == n and cs == ([i for i in range(1,d)]+[d*(2*d+2-n)]):
        #Folded cube
        return (5,n)
    
    return False

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
    H = GraphGenerators.EmptyGraph()
    queue = [G.vertices()[0]] # queue of vertex to follow
    H.add_vertex(G.vertices()[0])
    while queue:
        v = queue.pop(0)
        #compute all neighbours of the neighbours
        candidate = set([ x for c in G.neighbors(v,sort=False) for x in G.neighbors(c,sort=False) ])
        for w in candidate:
            if not G.has_edge(v,w):#then d(v,w)==2
                if w not in H:
                     queue.append(w)
                     H.add_vertex(w)
                H.add_edge(v,w)

    H.name("Halved %s" % G.name() )
    return H

def fold_graph( G, d=None):
    r"""
    Assume G is antipodal and computes its folded graph:

    G antipodal means G_d is a disjoint union of cliques
    (G_d is the distance graph of G and d is its diameter)

    the fold graph (V_f,E_f) is:
    V_f = maximal cliques of G_d
    E_f = { (c_1,c_2) | \exists u \in c_1, v \in c_2 s.t. (u,v) \in E }
    """

    distance = G.distance_all_pairs()

    if d is None:
        d= G.diameter()

    #go through vertices
    #if d(u,v) == d, then they are in a clique
    vertices = set(G.vertices(sort=False))
    cliques = []
    while vertices:
        v = vertices.pop()
        clique = [v]
        for u in vertices:
            if distance[v][u] == d:
                clique.append(u)

        vertices = vertices.difference(clique)
        #now we have a clique
        cliques.append(frozenset(clique))

    N = len(cliques)
    edges = []
    for i in range(N):
        cl1 = cliques[i]
        for j in range(i+1,N):
            cl2 = cliques[j]
            
            #look for edge connecting cliques
            edge=False
            for u in cl1:
                for v in cl2:
                    if G.has_edge((u,v)):
                        edge=True
                        break
                if edge:
                    break

            if edge:
                edges.append((i,j))
            
    H = Graph(edges,format="list_of_edges")
    H.name("Fold of %s" % (G.name()) )
    return H

def bipartite_double_graph(G):
    r"""
    This function return the biparite doubled graph of G
    the vertices of double graph are 2 copies of V
    the edges are (u_1,v_2), (u_2,v_1) for any (u,v) in E
    """
    #in order to have to copies of each vertex we do
    #(0,v) and (1,v)

    cdef list edges = []
    for (u,v) in G.edges(sort=False,labels=False):
        sig_check()
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
        sig_check()
        u1 = (0,u)
        u2 = (1,u)

        H.add_edge((u1,u2))

    H.name("Extended %s"%(H.name()))
    return H

################################################################################
# BIG FUNCTIONS THAT GROUP CONSTRUCTIONS
    
def pseudo_partition_graph(m,a):
    r""" p 198"""
    if a == 0:
        return GraphGenerators.FoldedCubeGraph(m)
    elif a == 1:
        return fold_graph(GraphGenerators.JohnsonGraph(2*m,m),d=m)
    elif a == 2:
        return fold_graph(half_cube(2*m),d=m)

    raise ValueError("no known graph exists")

def near_polygon_graph(const int g, t):
    r"""
    Returns a dist reg graph which is a near polygon with the given intersection array

    I NEED TO BE CAREFUL WITH ERRORS: invalid array or unknown graph????
    """
    if g == 0:
        if t[0] == 3:
            return generalised_hexagon(t[1],t[2])
        if t[0] == 4:
            return generalised_octagon(t[1],t[2])
        if t[0] == 6:
            return generalised_dodecagon(t[1],t[2])
        
    if g == 1:
        return GraphGenerators.CycleGraph(t)
    if g == 2:
        return GraphGenerators.OddGraph(t)
    if g == 3:
        return double_Grassmann_graph(*t)
    if g == 4:
        return doubled_odd_graph(t)
    if g == 5:
        return GraphGenerators.FoldedCubeGraph(t)

    raise ValueError(
            "{} {} is an incorrect input; use the function distance_regular_graph".format(g,t))

#list of pairs (f,g) s.t.
#if f(array) is not False, then g(*f(array)) should be a graph with the given intersection array
_infinite_families = [
    (is_classical_parameters_graph, graph_with_classical_parameters),
    (is_pseudo_partition_graph, pseudo_partition_graph),
    (is_near_polygon, near_polygon_graph),
    (is_hermitian_cover, hermitian_cover),
    (is_AB_graph, AB_graph),#this should be before Kasami graph for better performance
    (is_Preparata_graph, Preparata_graph),
    (is_Brouwer_Pasechnik_graph, Brouwer_Pasechnik_graph),
    (is_Pasechnik_graph, Pasechnik_graph),
    (is_from_association_scheme, graph_from_association_scheme),
    (is_from_GQ_spread, graph_from_GQ_spread),
    (is_symplectic_cover, symplectic_cover),
    (is_from_square_BIBD, graph_from_square_BIBD),
    (is_from_Denniston_arc, graph_from_Denniston_arc),
    (is_unitary_nonisotropic_graph, unitary_nonisotropic_graph),
    (is_Taylor_graph,Taylor_graph),
    (is_from_TD, graph_from_TD),
    (is_from_Kasami_code, Kasami_graph),
    (is_from_extended_Kasami_code, extended_Kasami_graph)
]

#given functions f,g
#returns function (f.g)
#f is expected to have only 1 input
def _compose(f,g):
    return lambda *x: f( g(*x) )

#dictionary intersection_array (as tuple)  -> construction
#of spordaic distance-regular graphs
_sporadic_graph_database = {
    (3, 2, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3) : GraphGenerators.FosterGraph,
    (7, 6, 4, 4, 4, 1, 1, 1, 1, 1, 1, 2, 4, 4, 6, 7) : IvanovIvanovFaradjev_graph,
    (3, 2, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3) : GraphGenerators.BiggsSmithGraph,
    (22, 21, 20, 16, 6, 2, 1, 1, 2, 6, 16, 20, 21, 22) : _compose(bipartite_double_graph, truncated_binary_Golay_code_graph),
    (23, 22, 21, 20, 3, 2, 1, 1, 2, 3, 20, 21, 22, 23) : _compose(bipartite_double_graph, binary_Golay_code_graph),
    (21, 20, 16, 6, 2, 1, 1, 2, 6, 16, 20, 21) : shortened_00_11_binary_Golay_code_graph,
    (21, 20, 16, 9, 2, 1, 1, 2, 3, 16, 20, 21) : shortened_000_111_extended_binary_Golay_code_graph,
    (22, 21, 20, 3, 2, 1, 1, 2, 3, 20, 21, 22) : shortened_binary_Golay_code_graph,
    (3, 2, 1, 1, 1, 1, 1, 1, 2, 3) : GraphGenerators.DodecahedralGraph,
    (22, 20, 18, 2, 1, 1, 2, 9, 20, 22) : shortened_extended_ternary_Golay_code_graph,
    (7, 6, 6, 1, 1, 1, 1, 6, 6, 7) : _compose(bipartite_double_graph, GraphGenerators.HoffmanSingletonGraph),
    (10, 9, 8, 2, 1, 1, 2, 8, 9, 10) : _compose(bipartite_double_graph, GraphGenerators.SimsGewirtzGraph),
    (16, 15, 12, 4, 1, 1, 4, 12, 15, 16) : lambda : bipartite_double_graph(GraphGenerators.strongly_regular_graph(77,16,0)),
    (22, 21, 16, 6, 1, 1, 6, 16, 21, 22) : _compose(bipartite_double_graph, GraphGenerators.HigmanSimsGraph),
    (3, 2, 2, 1, 1, 1, 1, 2) : Coxeter_graph,
    (6, 5, 5, 4, 1, 1, 2, 6) : LintSchrijver_graph,
    (7, 6, 4, 4, 1, 1, 1, 6) : doubly_truncated_Witt_graph,
    (9, 8, 6, 3, 1, 1, 3, 8) : distance_3_doubly_truncated_Golay_code_graph,
    (10, 8, 8, 2, 1, 1, 4, 5) : J2_graph,
    (11, 10, 6, 1, 1, 1, 5, 11) : GraphGenerators.LivingstoneGraph,
    (5, 4, 1, 1, 1, 1, 4, 5) : GraphGenerators.WellsGraph,
    (6, 4, 2, 1, 1, 1, 4, 6) : Foster_graph_3S6,
    (10, 6, 4, 1, 1, 2, 6, 10) : ConwaySmith_for_3S7,
    (20, 18, 4, 1, 1, 2, 18, 20) : shortened_ternary_Golay_code_graph,
    (45, 32, 12, 1, 1, 6, 32, 45) : locally_GQ42_graph,
    (117, 80, 24, 1, 1, 12, 80, 117) : graph_3O73,
    (22, 21, 20, 1, 2, 6): truncated_binary_Golay_code_graph,
    (23, 22, 21, 1, 2, 3): binary_Golay_code_graph,
    (24, 23, 22, 21, 1, 2, 3, 24): extended_binary_Golay_code_graph,
    (12,11,10,7,1,2,5,12): Leonard_graph,
    (15,14,10,3,1,5,12,15): cocliques_HoffmannSingleton,
    (27,10,1,1,10,27): GraphGenerators.GossetGraph,
    (30,28,24,1,3,15): large_Witt_graph,
    (15,14,12,1,1,9): truncated_Witt_graph,
    (24,22,20,1,2,12): extended_ternary_Golay_code_graph,
    (21,20,16,1,2,12): doubly_truncated_binary_Golay_code_graph,
}

def distance_regular_graph( list arr, existence=False, check=True ):
    import drg
    from drg import InfeasibleError

    def result(G):
        if check:
            array = intersection_array_from_graph(G)
            if array != arr:
                raise RuntimeError("Sage built the wrong distance-regular graph; expected {}, result {}".format(arr,array))
        return G

    def is_iterable(obj):
        try:
            iter(obj)
            return True
        except TypeError:
            return False

    n = len(arr)
    d = n // 2
    #check that arr makes sense:
    try:
        parameters = drg.DRGParameters(arr[:d],arr[d:])
    except (AssertionError, InfeasibleError, TypeError) as err:
        if existence: return False
        raise EmptySetError(
            "No distance-regular graphs with parameters {} exists; reason: {}".format(arr,err))

    #handle diameter < 3
    if d == 1 and arr[1] == 1:
        if existence: return True
        return result(GraphGenerators.CompleteGraph(arr[0]+1))
    if d == 2: 
        k = arr[0]
        mu = arr[3]
        l = k -arr[1]-1 #a1 = k - b1 -c1
        v = number_of_vertices_from_intersection_array(arr)
        if existence: return strongly_regular_graph(v,k,l,mu,existence=True)
        return result(strongly_regular_graph(v,k,l,mu))

    t = tuple(arr)
    if t in _sporadic_graph_database:
        if existence: return True
        return result(_sporadic_graph_database[t]())

    for (f,g) in _infinite_families:
        t = f(arr)
        if t is not False:
            if existence: return True
            
            G = g(*t) if is_iterable(t) else g(t)
            return result(G)

    #now try drg feasibility
    try:
        parameters.check_feasible()
    except (InfeasibleError, TypeError, AssertionError) as err:
        if existence: return False
        raise EmptySetError(
            "no distance-regular graph with intersection array {} exists; reason: {}".format(arr,feasible))
    
    if existence: return Unknown
    raise RuntimeError("No distance-regular graph with intersection array {} known".format(arr))

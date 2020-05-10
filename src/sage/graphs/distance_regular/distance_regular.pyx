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

from sage.categories.sets_cat import EmptySetError
from sage.misc.unknown import Unknown

from sage.graphs.distance_regular_codegraphs import coset_graph
from sage.graphs.distance_regular_sporadic import *

################################################################################
# UNBOUNDED DIAMETER

def graph_from_genHad(G,M):
    from sage.combinat.designs.difference_family import group_law
    from sage.categories.vector_spaces import VectorSpaces
    
    (identity, op, inverse) = group_law(G)
    n = len(M)
    n2 = n*n
    #first build skew symmetric from it
    RH = [ [0]*n2 for _ in range(n2)]
    for i in range(n):
        for j in range(n):
            for k in range(n):
                for l in range(n):
                    h1 = G(M[k][j])
                    h2 = G(M[i][l])
                    RH[n*i+j][n*k+l] = op(h1,inverse(h2))
    print("built RH")
    #vertices is {1,...,n} x G, n is size of M
    # (i,g) ~ (j,h) iff  and gM[i,j] = h


    
    edges = []
    for i in range(n2):
        for g in G:
            for j in range(i+ 1,n2):
                mij = RH[i][j]
                h = op(g,mij)
                if G in VectorSpaces:
                    g.set_immutable()
                    h.set_immutable()
                edges.append( ((i,g),(j,h)) )

    G = Graph(edges)
    return G
                
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

def test_dual_polar_orthogonal():

    numVer = lambda arr: number_of_vertices_from_intersection_array(arr)

    for d in range(3,10):
        for q in [2,3,4,5,7,8,9,11,13,16]:
            arr0 = intersection_array_from_classical_parameters(d,q,0,q)
            arr1 = intersection_array_from_classical_parameters(d,q,0,1)
            arrm1 = intersection_array_from_classical_parameters(d,q,0,q*q)

            if numVer(arr0) < 10000:
                print("(%d,%d,%d) = %d vertices"%(0,d,q,numVer(arr0)))
                G = dual_polar_orthogonal(0,d,q)
                print("(%d,%d,%d) built"%(0,d,q))
                if intersection_array_from_graph(G) != arr0:
                    print("failed parameters (%d,%d,%d)"%(0,d,q))

            if numVer(arr1) < 10000:
                print("(%d,%d,%d) = %d vertices"%(1,d,q,numVer(arr1)))
                G = dual_polar_orthogonal(1,d,q)
                print("(%d,%d,%d) built"%(1,d,q))
                if intersection_array_from_graph(G) != arr1:
                    print("failed parameters (%d,%d,%d)"%(1,d,q))

            if numVer(arrm1) < 10000:
                print("(%d,%d,%d) = %d vertices"%(-1,d,q,numVer(arrm1)))
                G = dual_polar_orthogonal(-1,d,q)
                print("(%d,%d,%d) built"%(-1,d,q))
                if intersection_array_from_graph(G) != arrm1:
                    print("failed parameters (%d,%d,%d)"%(-1,d,q))

    print("tested completed")
            

def dual_polar_orthogonal(const int e, const int  d, const int q):
    r"""
    return dual polar graph of type e with diameter d over GF(q)

    classical (d,q,0,q^{1-e}) e \in \{-1,0, 1\}
    """

    def hashable(v):
        v.set_immutable()
        return v

    if e not in {0,1,-1}:
        raise ValueError("e must by 0,+1 or -1")

    m = 2*d + 1 - e

    group = libgap.GeneralOrthogonalGroup(e,m,q)
    M = Matrix(libgap.InvariantQuadraticForm(group)["matrix"])

    #Q(x) = xMx is a quadratic form and group is the group of invertible linear transformation leaving Q invariant

    #we need to find a totally isotropic subspace of dimension n
    #attempt 1 (consider kernel)
    K = M.kernel()
    isotropicBasis = list(K.basis())

    assert(K.dimension() <= d, "isotropic subspace of dimension greater than d!!!")

    #otherwise extensive search?
    #or is K contained in a maximal isotropic subspace?
    #I think so since we state that all maximal isotropic have the same size
    #this hints that maximal means "can't be extended".
    #So we pick K and extend it to a maximal isotropic subspace
    if K.dimension() < d:
        print("need to extend K")
        V = VectorSpace(GF(q),m)
        candidates = set(map(hashable,V))
        toRemove = set()#set of vectors that are not candidates
        while K.dimension() < d:
            hashableK = set(map(hashable, K))
            candidates = candidates.difference(hashableK) #remove all isotropic vectors in K
            candidates = candidates.difference(toRemove)
            assert( candidates, "no candidate but K.dim < d")
            for v in candidates:
                if v*M*v == 0:
                    #found another isotropic point
                    #check if we can add it to K
                    #is enough to check crap on the basis (look at thesis)
                    ok = True
                    for w in isotropicBasis:
                        if w*M*v+v*M*w != 0:
                            ok = False
                            break
                        
                    if ok:
                        isotropicBasis.append(v)
                        K = V.span(isotropicBasis)
                    else:
                        #isotropic, but can't extend K
                        toRemove.add(v)
                else:
                    #not isotropic
                    toRemove.add(v)

        isotropicBasis = list(K.basis()) #we need vectors to be normalised

    #here K is a maximal totally isotropic subspace
    assert( len(isotropicBasis) == d, "something wrong with iso basis")

    
    #now use GAP for the job
    W = libgap.FullRowSpace(libgap.GF(q), m) #W is GAP version of V
    isoS = libgap.Subspace(W,isotropicBasis) #isoS is GAP version of K

    allIsoPoints = libgap.Orbit(group,isotropicBasis[0],libgap.OnLines) #assume group is transitive, we have all isotropic projective points

    permutation = libgap.Action(group, allIsoPoints,libgap.OnLines)
    #we make a permutation group s.t. the OnLines action of group on allIsoPoints is the same as the action of permutation on {1,2,...,|allIsoPoints|}
    #the above is just to speed things up to avoid matrix multiplications
    
    isoSPoints = [libgap.Elements(libgap.Basis(x))[0] for x in libgap.Elements(isoS.Subspaces(1))]
    #here we have a list of all projective points (represented as normalised vectors) in isoS (which is the maximal totally isotropic subspace)

    isoSPointsInt = libgap.Set([libgap.Position(allIsoPoints, x) for x in isoSPoints])
    #set of all integers representing the projective points of isoSPoints
    #this so that permutation can act on it

    allIsoSubspaces = libgap.Orbit(permutation,isoSPointsInt, libgap.OnSets)
    #assuming group was transitive on maximall isotropic subspaces, here we calculate the orbit of a maximal isotropic subspace
    #these are our vertices

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


def doubled_odd_graph( int n ):
    r"""
    let X = {1,2,..., 2n +1}
    The doubled odd graph is the graph with
    V = subsets of X of size n, n+1
    E = { (s1,s2) | s1 in s2 or s2 in s1 }

    This is WAY faster than building odd graph via Sage and then doubling it

    near polygon:
    diameter 2n+1
    b_i = (n+1)-c_i and c_{2i} = c_{2i-1} = i
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

    classical (\min (d,e), q, q-1 , q^{\max(d,e)}-1)

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
        # finally check if mat is a rank2 matrix
        if mat.rank() == 2:
            rank2Matrices.append(mat) # we append v as it is smaller than mat
    
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

def hermitean_form_graph(const int n, const int q):
    r"""
    Return the Hermitean from graph with the given parameters.

    We build a graph whose vertices are all ``n``x``n`` Hermitean matrices
    over ``GF(q)``. 2 vertices are adjecent if the difference of the 2 vertices
    has rank 1. We need ``q``=``r**2`` for some prime power ``r``

    classical (n, -sqrt{q}, -sqrt{q}-1, - (- sqrt{q})^d -1)

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

    (\lfloor \frac n 2 \rfloor, 1,2, 2 \lceil \frac n 2 \rceil -1)
    
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
    


def Grassmann( const int q, const int n, const int input_e ):
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
    cdef int size = (q**(e-1) -  1)/(q-1)
    G = PG.intersection_graph([size])
    G.name("Grassmann graph J_%d(%d,%d)"%(q,n,e))
    return G

def double_Grassmann(const int q, const int n, const int e):
    r"""
    vertices : e, e+1 dimensional subsets of (F_q)^n
    edges: (u,v) if u\neq v and (u \in v or v \in u)

    $b_i = (e+1)-c_i$ and $c_{2i} = c_{2i-1} = i$
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
    G.name("Double Grassmann graph (%d,%d,%d)"%(n,e,q))
    return G

################################################################################
# UNBOUNDED ORDER

def hermitean_cover(q,r):

    if not is_prime_power(q):
        raise ValueError("invalid input: q must be prime power")

    if (q*q-1)%r != 0:
        raise ValueError("r must divide q^2-1")

    if r%2 == 1 and (q-1)%r == 0:
        pass
    elif q%2 == 0 and (q+1)%r == 0:
        pass
    elif q%2 == 1 and ((q+1)//2)%r == 0:
        pass
    else:
        raise ValueError("invalid input")

    Fq2 = GF(q*q)
    V = VectorSpace(Fq2, 3)

    g = Fq2.primitive_element()
    Ksize = (q*q-1)// r
    Kgen = g**r
    K = set([ Kgen**i for i in range(Ksize)])
    
    Kset = {}
    Krep = {}
    for x in Fq2:
        if x.is_zero(): continue #0 not in Fq2^*
        xK = frozenset([ x*k for k in K])
        Kset[x] = xK
        Krep[xK] = x

    KrepSet = set()#set of representatives of Fq2/K
    for s in Krep:
        KrepSet.add(Krep[s])

    oneK = Krep[Kset[1]]

    #vertices are Kv for isotropic v
    GU = libgap.GU(3,q)
    J = Matrix(libgap.InvariantSesquilinearForm(GU)["matrix"])
    e1 = vector(Fq2,[1,0,0])

    iso_points = libgap.Orbit(GU,e1,libgap.OnLines)
    print(len(iso_points))

    vertices = [ (libgap(k),v) for k in KrepSet for v in iso_points ]
    print(len(vertices))

    gapActionOnVertices = libgap.eval("OnPairLines:= function( pair, g) return [pair[0],OnLines(pair[1],g)];end;")

    GUAction = libgap.Action(GU,vertices,gapActionOnVertices)

    e11 = vector(Fq2,[1,0,1])
    #(e1,e11) is an edge
    
    N = r*(q**3+1)
    print(N)
    
    edges = []
    for i in range(N):
        v = vertices[i]
        vq = [x**q for x in v]
        for j in range(i+1,N):
            u = vertices[j]
            Huv = u*J*vq# H(u,v)
            if Huv != 0 and  Krep[Kset[Huv]] == oneK:
                edges.append( (i,j) )
                
    G = Graph(edges, format="list_of_edges")
    return G

def is_AB_graph(arr):
    r"""
    Returns $n$ s.t. AB_graph(n) has intersection array $n$
    returns None otherwise
    """
    if len(arr) != 6: return None

    twoN = arr[0]+1 #2^n
    (p,n) = is_prime_power(twoN,get_data=True)
    if p != 2: return None

    #otherwise we found n
    if arr != [2**n-1,2**n-2,2**(n-1)+1,1,2,2**(n-1)-1]:
        return None
    
    return n

def test_AB_graph():
    import time
    
    for m in range(100):
        n = 2*m +1
        nV = 2**(2*n)
        if nV > 30000: break
        start = time.time()
        G = almost_bent_function_graph(n)
        end = time.time()
        if intersection_array_from_graph(G) != [2**n-1,2**n-2,2**(n-1)+1,1,2,2**(n-1)-1]:
            print("{} failed".format(n))
        else:
            print("{} with {} vertices in {}".format(n,nV,end-start))

    print("test done")

def AB_graph(const int n):
    r"""
    Graph using almost bent function on GF(2)^n
    """

    assert(n%2 ==1, "n should be odd; no AB known for n even")
    #if follows that (2,n) = 1

    Fq = GF(2**n)

    f = { x : x**3 for x in Fq}
        
    vectors = [x for x in Fq]

    edges = []
    for i,x in enumerate(vectors):
        for y in vectors[i+1:]:
            for a in vectors:
                b = a + f[x+y]
                edges.append(( (x,a),(y,b) ))
                edges.append(( (y,a),(x,b) ))

    G = Graph(edges,format="list_of_edges")
    return G

def is_Preparata_graph(arr):

    if len(arr) != 6: return
    q = (arr[0]+1) // 2
    (p,t) = is_prime_power(q,get_data=True)
    if p!= 2: return None
    t = (t+1) // 2 #so q = 2^{2t-1}
    
    p = arr[4]
    (r,i) = is_prime_power(p,get_data=True)
    if r != 2: return None
    i = i-1 #so p = 2^{i+1}

    if arr != [2*q-1,2*q-p,1,1,p,2*q-1]:
        return None

    return (t,i)

def test_Preparata():
    import time
    for t in range(1,100):
        for i in range(2*t-2,-1,-1):
            sig_check()
            q = 2**(2*t-1)
            Q = 2**(2*t-1-i)#size of Fq/A
            nV = 2*q*Q
            if nV > 10000:
                break
            start = time.time()
            G = Preparata_graph(t,i)
            end = time.time()
            twoi1 = 2**(i+1) 
            if intersection_array_from_graph(G) != [2*q-1,2*q-twoi1,1,1,twoi1,2*q-1]:
                print("%d %d failed"%(t,i))
            else:
                print("({},{}) with {} vertices in {}".format(t,i,nV,end-start))
    print("test done")

def Preparata_graph(t,i):
    r"""
    q= 2^(2t -1) |A| = 2^i
    """
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

def is_Brouwer_Pasechnik_graph(arr):
    if len(arr) != 6: return None
    q = arr[4]
    if not is_prime_power(q):
        return None
    if arr != [q**3-1,q**3-q,q**3-q**2+1,1,q,q**2-1]:
        return None
    return q

def test_Brouwer_Pasechink():
    import time
    for q in range(2,100):
        if not is_prime_power(q): continue
        if 2*(q**6) < 10000:
            start = time.time()
            G = Pasechnik_graph(q)
            end = time.time()
            if intersection_array_from_graph(G) != [q**3,q**3-1,q**3-q,q**3-q**2+1,1,q,q**2-1, q**3]:
                print("{} failed Pasechnik".format(q))
            else:
                print("Pasechnik {} with {} vertices in {}".format(q,2*(q**6),end-start))
        elif q**6 < 10000:
            start = time.time()
            G = Brouwer_Pasechnik_graph(q)
            end = time.time()
            if intersection_array_from_graph(G) != [q**3-1,q**3-q,q**3-q**2+1,1,q,q**2-1]:
                print("{} failed Brouwer_Pasechnik".format(q))
            else:
                print("Brouwer_Pasechnik{} with {} vertices in {}".format(q,2*(q**6),end-start))
        else: break
    print("test done")

def Brouwer_Pasechnik_graph(q):

    Fq = GF(q)

    def cross(v,w):
        z = [ v[1]*w[2]-v[2]*w[1], v[2]*w[0]-v[0]*w[2], v[0]*w[1]-v[1]*w[0] ]
        return vector(Fq,z)
            
    V = list(VectorSpace(Fq,3))
    for v in V:
        v.set_immutable()

    #ensuer V[0] is zero
    if not V[0].is_zero():
        for i in range(q**3):
            if V[i].is_zero():
                z = V[i]
                V[i] = V[0]
                V[0] = z

    edges = []
    for u in V:
        for v in V:
            for v2 in V:
                if v2 == v: continue #otherwise cross(v,v2) == 0 and u2 == u
                u2 = u+ cross(v,v2)
                u2.set_immutable()
                edges.append(( (u,v),(u2,v2) ))

    G = Graph(edges,format="list_of_edges")
    G.name("Brouwer-Pasechnik graph on GF(%d)"%q)
    return G

def is_Pasechnik_graph(arr):
    if len(arr) != 8: return None
    q = arr[5]
    if not is_prime_power(q):
        return None
    if arr != [q**3,q**3-1,q**3-q,q**3-q**2+1,1,q,q**2-1, q**3]:
        return None
    return q

def Pasechnik_graph(q):
    H = Brouwer_Pasechnik_graph(q)
    G = extended_biparitite_double_graph(H)
    G.name("Pasechnik graph on D_4(%d)"%q)
    return G
    

def test_schemes():
    import time
    for q in range(2,10000):
        if not is_prime_power(q): continue
        for r in Integer(q-1).divisors()[1:]:#r=1 -> complete graph
            if r*(q+1) > 10000: break
            S = cyclotomic_scheme(q,r)
            if ((q-1)//r)% 2 == 1 and is_prime_power(q,get_data=True)[0] != 2:
                #cyclotomic scheme is not symmetric
                if S.is_pseudocyclic():
                    print("({},{}) not symmetric but pseudocyclic".format(q,r))
                continue
            start = time.time()
            G = dist_reg_from_association_scheme(S)
            end = time.time()
            mu = (q-1)//r
            if intersection_array_from_graph(G) != [q,q-1-mu,1,1,mu,q]:
                print("({},{}) failed".format(q,r))
            else:
                print("({},{}) with {} vertices in {}".format(q,r,r*(q+1),end-start))
    print("test done")
            

class AssociationScheme:

    def _is_association_scheme(self):

        #check matrix size
        if self._matrix.ncols() != self._nX:
            print("matrix has wrong size")
        
        #check R0
        for i in range(self._nX):
            if self._matrix[i][i] != 0:
                print("identity is not R_0")
            
        
        #check symmetries
        for i in range(self._nX):
            for j in range(i+1,self._nX):
                if self._matrix[i][j] != self._matrix[j][i]:
                    print("not symmetric")
            

        #check intersection numbers
        self.compute_intersection_numbers()
        r1 = self._r+1
        for i in range(r1):
            Ri = self.R(i)
            for j in range(r1):
                Rj = self.R(j)
                for k in range(r1):
                    Rk = self.R(k)
                    pijk = self.p(i,j,k)
                    for (x,y) in Rk:
                        count = 0
                        for z in self._X:
                            if (x,z) in Ri and (z,y) in Rj:
                                count += 1
                        if pijk != count:
                            print("failed p{}{}{} with pair ({},{})".format(i,j,k,x,y))
                            return False
        return True
        
        
    def __init__(self, points, matrix, check=True):
        self._X = list(points)
        self._nX = len(self._X)
        self._XtoInt = { x: i for i,x in enumerate(self._X)}
        self._matrix = Matrix(matrix)

        #compute number of classes
        self._r = 0
        for r in self._matrix:
            for c in r:
                if c > self._r: self._r = c

        #empty intersection array
        r1 = self._r+1
        self._P = [ [ [None for k in range(r1) ] for j in range(r1)] for i in range(r1)]

        if check:
            if not self._is_association_scheme():
                raise ValueError("input given is not an association scheme")
            

    def ground_set(self):
        return self._X

    def num_points(self):
        return self._nX

    def matrix(self):
        return self._matrix

    def num_classes(self):
        return self._r

    def has_relation(self,x,y,i):
        return self.which_relation(x,y)  == i

    def which_relation(self,x,y):
        return self._matrix[self._XtoInt[x]][self._XtoInt[y]]
    
    def R(self,i):
        Ri = set()
        for i in range(self._nX):
            for j in range(i+1,self._nX):
                if self._matrix[i][j] == i:
                    Ri.add((self._X[i],self._X[j]))
                    Ri.add((self._X[j],self._X[i]))

        return Ri

    def p(self,i,j,k):
        if self._P[i][j][k] is not None: return self._P[i][j][k]

        r1 = self._r+1

        self._P[i][j][k] = 0
        for x in range(r1):
            for y in range(r1):
                if self._matrix[x][y] == k:
                    break
            else:
                continue
            break

        assert(self._matrix[x][y] == k, "something wrong")

        #now (x,y) in R_k
        for z in range(r1):
            if self._matrix[x][z] == i and self._matrix[z][y] == j:
                self._P[i][j][k] += 1

        return self._P[i][j][k]
        

    def compute_intersection_numbers(self):
        if self._P is not None: return
        r1 = self._r+1
        for i in range(r1):
            for j in range(r1):
                for k in range(r1):
                    self.p(i,j,k)

    def is_pseudocyclic(self):
        #we need p_{ii}^0 to be a constant f for 1<= i <= r
        #we need sum_{i} p_{ii}^k = f-1 for 1 <= k <= r
        r1 = self._r+1
        f = self.p(1,1,0)
        for i in range(2,r1):
            if self.p(i,i,0) != f:
                return False

        for k in range(1,r1):
            sumP = 0
            for i in range(r1):
                sumP += self.p(i,i,k)

            if sumP != f-1:
                return False
        return True


def cyclotomic_scheme(q,r,check=False):
    #for (q-1)/r even or q power of 2, then the association scheme is symmetric
    #and pseudocyclic

    assert( (q-1)%r == 0, "q=rm+1 is not respected")

    Fq = GF(q)
    X = list(Fq)
    XtoInt = { x: i for i,x in enumerate(X) }
    
    relations = [ [0 for i in range(q)] for j in range(q)] #qxq matrix

    a = Fq.primitive_element()
    ar = a**r
    m = (q-1)//r
    K = [ ar**i for i in range(m)]
    for i in range(1,r+1):
        ai=a**i
        aiK = [ ai*x for x in K]
        for x in X:
            for z in aiK:
                y = x+z
                relations[XtoInt[x]][XtoInt[y]] = i

    return AssociationScheme(X,relations,check)

def is_from_association_scheme(arr):
    r"""
    Return (n,r) is the graph built from an r-class association scheme of size n
    has interseciont array arr
    """
    if len(arr) != 6: return None
    n = arr[0]
    mu = arr[4]
    r = (n-1) // mu
    if arr != [n,(r-1)*mu,1,1,mu,n]:
        return None
    return (n,r)

def graph_from_association_scheme(scheme, inf = "inf"):
    r"""
    we assume inf is not in the ground set of scheme
    """
    assert( inf not in scheme.ground_set(), "a must not be in the scheme")

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

def is_from_GQ_spread(arr):
    r"""
    Returns (s,t) s.t. the graph obtained from a GQ of order (s,t) with a spread
    has the correct intersection array
    """
    if len(arr) != 6: return None
    t = arr[4]+1
    s = arr[1] // (t-1)
    if arr != [s*t,s*(t-1),1,1,t-1,s*t]:
        return None
    return (s,t)

def test_GQ_graphs():

    import time
    
    for q in [2,3,4,5,7,8,9]:
        start = time.time()
        (GQ,O) = generalised_quadrangle_hermitean(q)
        end = time.time()
        print("constructed GQ H(3,{}^2)with {} points in {}".format(q,GQ.num_points(),end-start))
        
        start = time.time()
        G = dist_reg_from_GQ_ovoid(GQ,O)
        end = time.time()
        if intersection_array_from_graph(G) != [q**3,q*((q**2)-1),1,1,(q**2)-1,q**3]:
            print("!!!!!!!!!graph {} failed!!!!!!!!!!!".format(q))
        else:
            print("construced graph with {} edges in {}".format(G.size(),end-start))

    print("done test")

def graph_from_GQ_spread(GQ, S):
    r"""
    point graph of the generalised quadrangle without its spred
    """
    k = len(GQ.blocks()[0])
    edges = []
    for b in GQ.blocks():
        if b in S: continue
        for i in range(k):
            p1 = b[i]
            for j in range(i+1,k):
                p2 = b[j]
                edges.append( (p1,p2) )

    G = Graph(edges, format="list_of_edges")
    return G

def graph_from_GQ_ovoid(GQ,ovoid):
    r"""
    Given a gen quadrangle with an ovoid, we compute the graph
    that we would get from its dual with a spread
    """

    #vertices are lines of GQ
    #2 lines are adjecent if their instersection is non-empty and is not in ovoid
    #so we could remove ovoid from all lines and then only worry about non-emptyness
    setOvoid = set(ovoid)

    newBlocks = [ set(line).difference(setOvoid) for line in GQ.blocks() ]
    
    edges = []
    for i,line in enumerate(newBlocks):
        sline = set(line)
        for j in range(i+1,GQ.num_blocks()):
            line2 = newBlocks[j]
            if sline.intersection(line2):
                edges.append( (i,j) )

    G = Graph(edges,format="list_of_edges")
    return G


def generalised_quadrangle_hermitean(q):
    r"""
    Another way of making H(3,q^2)
    """

    GU = libgap.GU(4,q)
    H = libgap.InvariantSesquilinearForm(GU)["matrix"]
    Fq = libgap.GF(q*q)
    zero = libgap.Zero(Fq)
    one = libgap.One(Fq)
    V = libgap.FullRowSpace(Fq,4)

    e1 = [one,zero,zero,zero] #isotropic point
    assert( e1*H*e1 == zero, "e1 not isotropic")
    print("found iso point")

    points = list(libgap.Orbit(GU,e1,libgap.OnLines)) #all isotropic points
    pointInt = { x:(i+1) for i,x in enumerate(points) } #+1 because GAP starts at 1
    #points is the hermitean variety

    GUp = libgap.Action(GU, points, libgap.OnLines)#GU as permutation group of points

    e2 = [zero,one,zero,zero]
    #we have totally isotropic line
    line = V.Subspace([e1,e2])
    lineAsPoints = [libgap.Elements(libgap.Basis(b))[0] for b in libgap.Elements(line.Subspaces(1)) ]
    line = libgap.Set([ pointInt[p] for p in lineAsPoints ])
    print("found iso line")

    lines = libgap.Orbit(GUp, line, libgap.OnSets)#all isotropic lines
    #print(len(lines))

    #to find ovoid, we embed H(3,q^2) in H(4,q^2)
    #then embedding is (a,b,c,d) -> (a,b,0,c,d) [so we preserve isotropicity]
    #then find a point in the latter and not in the former
    #this point will be collinear in H(3,q^2) to all (and only) the points in a ovoid
    W = libgap.FullRowSpace(Fq,5)
    J = [ [0,0,0,0,1],[0,0,0,1,0],[0,0,1,0,0],[0,1,0,0,0],[1,0,0,0,0]]
    J = libgap(J)
    if q%2 == 1:
        (p,k) = is_prime_power(q,get_data=True)
        a = (p-1)// 2
        aGap = zero
        for i in range(a):
            aGap += one
        p = [zero,one,one,aGap,zero]
    else:
        a = libgap.Z(q*q)**(q-1)
        p = [zero,one,a+one,a,zero]
        
    print("building ovoid")
    #now p is a point of H(4,q^2)

    #p' is collinear to p iff p'Jp^q = 0
    #note that p'Jp^q = bx^q + c where p' =(a,b,0,c,d) and p=(0,1,1,x,0)
    #hece we have points (0,0,0,1); (0,1,c,a) for any a iff c^q+c = 0 (c = -x^q)
    #and (1,b,c,x) for any x and any b (c= -bx^q) iff it is an iso point
    #so we need only q^2 (for last case) +1 (for 2nd case) checks 
    ovoid = []
    xq = p[3]**q
    for p2 in points:
        if p2[1]*xq+p2[2] == zero: #p collinear to newP2
            ovoid.append(libgap(pointInt[p2]))

    from sage.combinat.designs.incidence_structures import IncidenceStructure
    D = IncidenceStructure(lines)
    return (D,ovoid)

def is_ovoid(D,ovoid):
    setOvoid = set(ovoid)
    for line in D.blocks():
        l = [Integer(x) for x in line]
        if len(setOvoid.intersection(l)) != 1:
            print(line)
            return False

    return True


def test_symplectic():
    import time
    
    for q in [16,17,19,23,25,27]:
        for r in Integer(q).divisors()[1:]:#this removes the case r = 1
            for n in range(2,20,2):
                arr = [q**n-1,(r-1)*q**n/r,1,1,q**n/r, q**n-1]
                nV = number_of_vertices_from_intersection_array(arr)
                if nV < 10000:
                    start = time.time()
                    G = symplectic_cover_of_complete(q,n,r)
                    end = time.time()
                    if intersection_array_from_graph(G) != arr:
                        print("{} {} {} failed".format(q,n,r))
                    else:
                        print("{} {} {} with {} vertices done in {}".format(q,n,r,nV,end-start))
                else:
                    break
    print("test done")

def is_generalised_symplectic_cover(arr):
    if len(arr) != 6: return None
    qn = arr[0]+1
    r = qn // arr[4]
    if r == 1: return None
    if arr != [qn-1,((r-1)*qn)//r,1,1,qn//r,qn-1]:
        return None
    
    (p,k) = is_prime_power(qn,get_data=True)
    if not is_prime(p):
        return None #q not a prime power
    #q^n = p^k

    #n even -> k even
    if k%2 == 1: return None
    if qn%r != 0: return None 
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
        return None
    return (q,n,r)

def generalised_symplectic_cover(const int q, const int n, r = None):
    r"""
    (q,n,r) build a dist reg graph. If r == q, then we have a antipodal q cover of K_q^n
    """
    if r == None:
        r = q
    assert(n%2 == 0, "n must be even")
    assert(q%r == 0 and r != 1, "r must be a factor of q and not 1")

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
        Adim = Fqvec.dimension() -k
        A = Fqvec.span([ei(i,Fqvec.dimension()) for i in range(Adim)])
        A = [ fromVec(x) for x in A ]

        Q = set()
        toQ = {}# map a -> a+A
        Qrep = {}#map a+A -> a (pick unique representative for each a+A)
        for x in Fq:
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
                a = b + Bxy
                a2 = b + Byx
                if r != q:
                    a = Qrep[toQ[a]]
                    a2 = Qrep[toQ[a2]]
                   
                edges.append( ( (a,x),(b,y) ) )
                edges.append( ( (a2,y),(b,x) ) )

    G = Graph(edges, format="list_of_edges")
    G.name("antipodal %d cover of K_{%d^%d}"%(q,q,n))#to be changed
    return G

def is_from_BIBD(arr):
    if len(arr) != 6: return None
    k = arr[0]
    l = arr[4]
    v = (k*(k-1))//l +1

    if arr != [k, k-1, k-l, 1,l,k]:
        return None

    return (v,k)

def graph_from_BIBD(v,k):
    lmbd = (k*(k-1))//(v-1) #the division should not trucate
    D = Sage_Designs.balanced_incomplete_block_design(v,k,lmbd=lmbd)
    return D.incidence_graph()

def is_from_Denniston_arc(arr):
    if len(arr) != 8: return None
    n = arr[3]
    (p,k) = is_prime_power(n,get_data=True)
    if p != 2: return None

    if arr != [n*n-n+1,n*(n-1),n*(n-1),n,1,1,(n-1)**2,n*n-n+1]:
        return None
    return n

def graph_from_Denniston_arc(n):
    r"""
    build dist reg graph from p387
    """
    (p,k) = is_prime_power(n,get_data=True)
    if p != 2:
        raise ValueError("input must be a power of 2")
    
    q = n*n
    Fq = GF(q)
    Fn = GF(n)
    elemsFq = [ x for x in Fq]
    assert(elemsFq[0] == 0, "issue with 0 in Fq")

    #find irreducible quadratic
    candidates = set(Fq)
    for x in elemsFq[1:]:#we rely on the first element to be 0
        a = x + (1/x)
        candidates = candidates.difference({a})

    irrCoef = candidates.pop()
    print("irr quadric: x^2+{}xy+y^2".format(irrCoef))
    def Q(x,y):
        return x*x+irrCoef*x*y+y*y

    PG = Sage_Designs.ProjectiveGeometryDesign(2,1,q) #projective plane PG(2,q)
    #the points are represented as vectors with homogenous coordinates (first non-zero entry is 1)

    arc = set() #complete arc                
    for v in PG.ground_set():
        if v[0] == 1 and Q(v[1],v[2]) in Fn:
            arc.add(v)

    #pick all lines intersecting arc in n points (so any line intersecting the arc)
    #remove all points in arc
    lines = []
    for b in PG.blocks():
        sb = Set(b)
        for p in b:
            if p in arc:
                newLine = sb.difference(arc)
                lines.append(newLine)
                break

    #now we have a list of all lines of the complement
    edges = []
    for b in lines:
        bs = Set(b)
        for p in b:
            edges.append( (p,bs) )

    G = Graph(edges,format="list_of_edges")
    G.name("Incidence graph of the complement of a complete %d-arc in PG(2,%d)"%(n,q))
    return G

def is_unitary_nonisotropic_graph(arr):
    if len(arr) != 6: return None
    q = arr[2]-1
    if not is_prime_power(q):
        return None
    if q <= 2: return None

    if arr != [q*q-q,q*q-q-2,q+1,1,1,q*q-q]:
        return None
    return q

def unitary_nonisotropic_graph(q):
    r"""
    see page 383 on BCN
    """
    if q < 3:
        raise ValueError("q must be greater than 2")
    if not is_prime_power(q):
        raise ValueError("q must be a prime power")
    
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

def is_Taylor_graph(arr):
    r"""
    returns (n,l) s.t. the regular two-graph over $n$ points (i.e. the two-graph which is a 2-design(n,3,l) )
    taylor_twograph(q) has q^3+1 vertices and l = (q-1)(q^2+1)/2  [for reason look at paper referenced in sage doc about taylor_twograph]
    where any 2 points are in l blocks construct the distance-regular graph we want
    """
    if len(arr) != 6: return None
    k = arr[0]
    mu = arr[1]
    if arr != [k,mu,1,1,mu,k]:
        return None
    v = number_of_vertices_from_intersection_array(arr)
    n = v//2
    #two-graph has $n$ points
    l = k - mu-1 #any 2 points are in a1 triangles
    #hence any 2 points are in l blocks
    return (n,l)

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

def is_from_TD(arr):
    if len(arr) != 8: return None

    u = arr[5]
    m = arr[0]//u

    if arr!=[m*u,m*u-1,(m-1)*u,1,1,u,m*u-1,m*u]:
        return None
    return (m,u)

def graph_from_TD(m,u):
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
        lines.append(tuple(bottom2))
        
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
            if set(l1).intersection(l2) :
                edges.append( (l1,l2) )
            
    G = Graph(edges, format='list_of_edges')
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
        if q> 3: raise ValueError("graph is too big")
        movedPoints = 819 if q==2 else 26527
        group = libgap.AtlasGroup("3D4(%d)"%q,libgap.NrMovedPoints,movedPoints)
        G = Graph(group.Orbit([1,2],libgap.OnSets), format='list_of_edges')
        G.name("Generalised hexagon of order (%d,%d)"%(q,q**3))
        return G
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

def test_Kasami_graphs():
    r"""
    build all kasami graphs of type i for v < 10000
    """

    from sage.arith.misc import gcd
    
    for i in range(1,20):
        q = 2**i
        for j in range(1,20):
            s = q**(2*j+1)
            for m in range(j+1):
                if gcd(m,2*j+1) != 1: continue

                t = q**m

                extended_v = 2*q**(4*j+2)
                v = q**(4*j+2)

                if extended_v < 10000:
                    G = extended_Kasami_graph(s,t)
                    if intersection_array_from_graph(G) != [q**(2*j+1), q**(2*j+1)-1, q**(2*j+1)-q, q**(2*j)*(q-1)+1, 1, q, q**(2*j)-1, q**(2*j+1)]:
                        print("extended code failed values (q,j,m) (%d,%d,%d)"%(q,j,m))
                    else:
                        print("extended (q,j,m) (%d,%d,%d) (%d vertices) passed"%(q,j,m,extended_v))

                if v < 10000:
                    G = Kasami_graph(s,t)
                    if intersection_array_from_graph(G) !=  [q**(2*j+1)-1, q**(2*j+1)-q, q**(2*j)*(q-1)+1, 1, q, q**(2*j)-1]:
                        print("failed values (q,j,m) (%d,%d,%d)"%(q,j,m))
                    else:
                        print("(q,j,m) (%d,%d,%d) (%d vertices) passed"%(q,j,m,v))

    print("test completed")

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

def is_from_Kasami_code(arr):
    if len(arr) != 6: return None
    q = arr[4]
    (p,k) = is_prime_power(q,get_data=True)
    if p != 2: return None

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
    if qn > qk: return None
    if n%2 == 0: return None
    j = (n-1) //2

    if arr == [q**(2*j+1)-1,q**(2*j+1)-q,q**(2*j)*(q-1)+1,1,q,q**(2*j)-1]:
        return (q**(2*j+1),q)

    return None

def Kasami_graph(s,t):
    K = Kasami_code(s,t)
    G = coset_graph(2,K.basis(),n=s-1)
    G.name("Coset graph of Kasami code (%d,%d)"%(s,t))
    return G

def is_from_extended_Kasami_code(arr):
    if len(arr) != 8: return None
    q = arr[5]
    (p,k) = is_prime_power(q,get_data=True)
    if p != 2: return None

    if arr == [q*q, q*q-1, q*q-q,1,1,q,q*q-1,q*q]:
        return (q*q,q)

    qk = arr[0]
    n=1
    qn = q
    while qn < qk:
        n += 1
        qn *= q
    if qn > qk: return None
    if n%2 == 0: return None
    j = (n-1)//2

    if arr == [q**(2*j+1),q**(2*j+1)-1,q**(2*j+1)-q,q**(2*j)*(q-1)+1,1,q,q**(2*j)-1,q**(2*j+1)]:
        return (q**(2*j+1),q)

    return None

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

def is_classical_parameters_graph( array ):
    r"""
    Return the classical parameters ``(d,b,alpha,beta)`` 
    representing the intersection array.

    This function will check whether given array is an itersection array 
    that can be represented with classical parameters.

    INPUT:

    - ``array`` -- array of integers


    OUTPUT:
    
    tuple ``(d,b,alpha,beta)`` of classical parameters for array if the array has classical parameters
    None otherwise

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
    if len(array) % 2 != 0 : return None
    
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
        return None
    
    (alpha,beta) = getAlphaBeta(b)
    
    if not checkValues(array, d, b, alpha, beta):
        return None
    
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
    if the array is no good, then returns None
    p197

    we only handle d >= 3
   

    """
    d = len(arr)
    if d % 2 != 0:
        return None

    d = d // 2

    if d < 3 :
        return None
    
    #m = 2*d or 2*d +1
    #b_i = (m-i)(1 + a(m-1-i)) for i < d
    #c_i = i(1+ a(i-1)) for i < d
    #b_d = 0; c_d = g*d(1+a(d-1)) where g = m % 2

    #c_2 = 2 ( 1+a)
    c2 = arr[d+1]
    if c2 % 2 != 0:
        return None
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

    return None

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
        return None

    d = d // 2
    
    if arr[d] != 1: #c_1 = 1 ALWAYS
        return None

    k = arr[0]
    l = (k - arr[1]) - 1
    
    #for i = 0 we have b_0 = k - (l+1)*c_0 = k since c_0 = 0 always
    # we check i = 1 since in our expression for l we use integer division
    for i in range(1,d):
        if arr[i] != k - (l+1)*arr[d+i-1]: #b_i = k - (l+1)c_i
            return None

    #finally chek k >= (l+1)c_d
    if k < (l+1)*arr[2*d-1]:
        return None
    
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

def graph_with_classical_parameters( const int d,
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
        elif d == 3 and alpha == -3 and beta == 7:
            return doubly_truncated_binary_Golay_code_graph()
    
    elif b < 0 and is_prime_power(b):
        if alpha +1 == (1 + b*b)/(1 + b) and beta +1 == q_binomial(d+1,1,b):
            # U(2d,r)
            return GraphGenerators.UnitaryDualPolarGraph(2*d,-b)
        elif d == 3 and alpha + 1 == 1 / (1+b) and beta + 1 == q_binomial(3,1,-b):
            q = -b
            if q < 4:
                return generalised_hexagon(q,q**3)
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
            n = is_power_of( (beta+1)*(b-1)+2,b)+d-1
            return Grassmann(b,n,d)
        elif alpha == 0 and is_power_of( beta, b ) in {0, 0.5, 1, 1.5, 2}:
            # dual polar graphs
            e = is_power_of( beta, b )
            if e == 0:
                #maximal Witt index
                return dual_polar_orthogonal(1,d,b)
            if e == 1:
                #dual sympletic
                return GraphGenerators.SymplecticDualPolarGraph(2*d, b)
            elif e == 2:
                #non maximal Witt index
                return dual_polar_orthogonal(-1,d,b)
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
            q = q_of(b,2)
            m = is_power_of( (beta+1)*(q-1) +1, q) -1
            Ustimenko_graph(m,q)
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

def near_polygon_graph(list arr):
    r"""
    Returns a dist reg graph which is a near polygon with the given intersection array

    I NEED TO BE CAREFUL WITH ERRORS: invalid array or unknown graph????
    """
    def is_generalised_2d_gon(a):
        d = len(a)/2
        #c_1,...,c_{d-1} = 1
        for i in range(1,d):
            if a[d+i-1] != 1: return None

        t = a[2*d-1] -1 #c_d-1
        
        # b_0 = s(t+1)
        if a[0] % (t+1) != 0: return None
        s = a[0] // (t+1)

        #b_i = st
        for i in range(1,d):
            if a[i] != s*t: return None

        #otherwise we have it
        return (s,t)

    d = len(arr)
    l = is_near_polygon(arr)
    if l is None:
        raise ValueError("no near polygon known with such intersection array")

    if d < 3:
        raise ValueError("we only handle diameter >= 3")

    d = d // 2
    k = arr[0]

    if k == (l+1)*arr[2*d-1]:
        n = 2*d
    else:
        n = 2*d +1

    if k == 2 and l == 0:
        #polygon, but still check c_i's
        for i in range(1,d):
            if arr[d-1+i] != 1:
                raise ValueError("no near polygon known with such intersection array")
        if arr[2*d-1] != 2*d+2 - n : #c_d = \gamma = 1 if n odd and 2 if n even
            raise ValueError("no near polygon known with such intersection array")

        return GraphGenerators.CycleGraph(n)

    if l == 0 and k == d+1 and n == 2*d +1:
        #odd graph
        #still check c_i's
        for i in range(1,d+1):
            #c_{2j} = j
            #c_{2j -1} = j
            #so c_i = (i+1) // 2
            if arr[d-1+i] != (i+1) // 2:
                raise ValueError("no near polygon known with such intersection array")

        #what I call Odd(n) is Odd(n+1) in Sage
        return GraphGenerators.OddGraph(d+1)
    if l == 0 and n == 2*d:
        #R3 (double grassman or odd)
        if d % 2 == 0:
            raise ValueError("no near polygon known with such intersection array")
        e = (d-1) // 2
        if k == e+1:
            #double odd
            #c_i need to satisfies the same as above
            for i in range(1,d+1):
                if arr[d-1+i] != (i+1) // 2:
                    break #not double odd
            else:# we have double odd
                #I postulate that doubled_odd_graph(x) has diameter 2*x +1
                #I should prove it
                return doubled_odd_graph(e)
        
        #we have double grassman (since it is not double odd)
        #k = q_binomial(e+1,1,q) for some prime power q
        #c_j = q_binomail( (j+1)//2, 1, q)
        #so c_3 = q_binomial( 2,1,q) = q+1
        #we need d >= 3
        q = arr[d-1+3] -1
        if not is_prime_power(q) or k != q_binomial(e+1,1,q):
            raise ValueError("no near polygon known with such intersection array")

        #now check c_i's
        for i in range(1,d+1):
            if arr[d-1+i] != q_binomial( (i+1)//2, 1,q):
                raise ValueError("no near polygon known with such intersection array")
        #note that the diameter of the double grassman graph (q',n',e')
        #is n'
        return double_Grassmann(q,d,e)

    if k == n and l == 0:
        #folded cube
        for i in range(1,d):
            if arr[d-1+i] != i:
                raise ValueError("no near polygon known with such intersection array")
        if arr[2*d-1] != (2*d+2-n)*d:
            raise ValueError("no near polygon known with such intersection array")
        
        return fold_graph(GraphGenerators.HammingGraph(n,2))

    if k == d*(l+1) and n== 2*d and arr[d+1] == 2:
        #hamming graph
        for i in range(1,d+1):
            if arr[d-1+i] != i:
                raise ValueError("no near polygon known with such intersection array")
        return GraphGenerators.HammingGraph(d,l+2)

    #if dual polar, then
    q = arr[d+1]-1 #c2 = q+1
    if k == (l+1)*(q**d -1)//(q-1) and n == 2*d:
        #dual polar graph
        t = is_classical_parameter_graph(arr)
        if t is None:
            raise ValueError("no near polygon known with such intersection array")
        return graph_with_classical_parameters(*t)

    pair = is_generalised_2d_gon(arr)
    if pair is not None:
        if d == 3:
            return generalised_hexagon(*pair)
        elif d == 4:
            return generalised_octagon(*pair)
        elif d == 6:
            return generalised_dodecagon(*pair)

    #could also have partition graph
    #could be classical parameters
    
    raise ValueError("no near polygon known with such intersection array")

#list of pairs (f,g) s.t.
#if f(array) is not None, then g(*f(array)) should be a graph with the given intersection array
_infinite_families = [
    (is_classical_parameters_graph, graph_with_classical_parameters),
    (is_pseudo_partition_graph, pseudo_partition_graph),
    (is_near_polygon, near_polygon_graph),
    (is_AB_graph, AB_graph),
    (is_Preparata_graph,Preparata_graph),
    (is_Brouwer_Pasechnik_graph,Brouwer_Pasechnik_graph),
    (is_Pasechnik_graph,Pasechnik_graph),
    (is_from_association_scheme,graph_from_association_scheme),#needs func to create association scheme
    (is_from_GQ_spread,graph_from_GQ_spread),#needs func to create GQ
    (is_generalised_symplectic_cover,generalised_symplectic_cover),
    (is_from_BIBD,graph_from_BIBD),
    (is_from_Denniston_arc,graph_from_Denniston_arc),
    (is_unitary_nonisotropic_graph,unitary_nonisotropic_graph),
    (is_Taylor_graph,graph_from_two_design), #needs func to crete regular two-graph
    (is_from_TD,graph_from_TD),
    (is_from_Kasami_code,Kasami_graph),
    (is_from_extended_Kasami_code,extended_Kasami_graph)
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
	(117, 80, 24, 1, 1, 12, 80, 117) : graph_3O73
}

def distance_regular_graph( list arr, existence=False, check=True ):
    import drg

    def is_feasible(array):
        try:
            parameters = drg.DRGParameters(array[:d],array[d:])
            parameters.check_feasible()
        except:
            return False
        return True

    def result(G):
        if check:
            array = intersection_array_from_graph(G)
            if array != arr:
                raise RuntimeError("Sage built the wrong distance-regular graph; expected {}, result {}".format(arr,array))
        return G
    
    n = len(arr)    

    d = n // 2

    if not is_feasible(arr):
        if existence:
            return False
        raise EmptySetError("no such graph exists")
    print("is feasible")
    
    if d == 1:
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
        print("in sporadic database")
        if existence: return True
        return result(_sporadic_graph_database[t]())

    for (f,g) in _infinite_families:
        t = f(arr)
        if t is not None:
            print("found a family {}".format(f))
            try:
                G = g(*t)
            except:
                continue #try other constructions
            
            #here graph was built (may need to improve to avoid long times)
            if existence: return True
            return result(G)
    arr == [12,11,10,7,1,2,5,12]
    #leonard graph

    raise Unknown("Don't know anything about distance-regular graphs with intersection array {}".format(arr))

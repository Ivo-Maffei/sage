r"""
all dist reg graph with unbounded diameter
"""

from sage.combinat.integer_vector import IntegerVectors
from sage.graphs.graph import Graph
from sage.matrix.matrix_space import MatrixSpace
from sage.rings.finite_rings.finite_field_constructor import GF
from cysignals.signals cimport sig_check
from sage.arith.misc import is_prime_power
from sage.graphs.graph_generators import GraphGenerators
from sage.combinat.designs import design_catalog as Sage_Designs

def _hamming_distance( v, w ):
    assert( len(v) == len(w),
         "Can't compute Hamming distance of 2 vectors of different size!")
         
    cdef int counter = 0
    for i in range(len(v)):
        if ( v[i] != w[i] ):
            counter = counter + 1
    
    return counter

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
    #construct the halved cube graph 1/2 Q_n ( = Q_{n-1} ^2 )
    G = GraphGenerators.CubeGraph(n-1)
    # now square the graph
    # we use the fact that the vertices are strings and their distance is their hamming_distance
    for i in G.vertices():
        for j in G.vertices():
            sig_check()
            if _hamming_distance(i, j) == 2 :
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


# cython: profile=False
# -*- coding: utf-8 -*-
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.modules.free_module import VectorSpace
from sage.matrix.constructor import Matrix
from sage.modules.free_module_element import vector
from sage.graphs.graph import Graph
from sage.graphs.graph_generators import GraphGenerators
from sage.coding import codes_catalog as codes


r"""
Include all graphs built as cosets graphs from linear codes
"""
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


###########################################################################
# Below sporadic linear code graphs

def extended_ternary_Golay_code_graph():
    r"""
    Return the graph associated with the extended ternary Golay code.

    The graph constructed has  the codewords of
    the extended ternary Golay code as vertices.
    2 vertices are adjecent if their difference is a codeword of
    hamming weight 12.

    EXAMPLES:

        sage: g = extended_ternary_Golay_code_graph()
        sage: g.is_distance_regular()
        True

    TESTS::
    """

    V = VectorSpace(GF(3),12) # underlying vectorspace
    C = V.span([ (1, 0, 0, 0, 0, 0, 2, 0, 1, 2, 1, 2),
                 (0, 1, 0, 0, 0, 0, 1, 2, 2, 2, 1, 0),
                 (0, 0, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1),
                 (0, 0, 0, 1, 0, 0, 1, 1, 0, 2, 2, 2),
                 (0, 0, 0, 0, 1, 0, 2, 1, 2, 2, 0, 1),
                 (0, 0, 0, 0, 0, 1, 0, 2, 1, 2, 2, 1) ])
    # C is the codeword space
    
    G = GraphGenerators.EmptyGraph()
    G.add_vertices( map( tuple, C ) )

    generators = [ v for v in C if v.hamming_weight() == 12 ]

    for v in G:
        for s in generators:
            w = tuple( map( sum , zip(v,s) ))
            G.add_edge(v,w)
            
    G.name("Ternary Extended Golay Code Graph")
    return G

def extended_binary_Golay_code_graph():
    # e(i) creates the vector e_i
    def e(const int i):
        v = [0]*24
        v[i-1] = 1
        return vector(GF(2),v)

    U_basis = [ e(i) for i in range(1,13) ]

    golayCode = codes.GolayCode(GF(2), extended=True)
    C_basis = list( golayCode.generator_matrix() )

    G = coset_graph(2,C_basis,U_basis)
    G.name("Extended Binary Golay code graph")
    return G
    
def binary_Golay_code_graph():
    r"""
    construction as above
    """

    # e(i) creates the vector e_i
    def e(const int i):
        v = [0]*23
        v[i-1] = 1
        return vector(GF(2),v)

    U_basis = [ e(i) for i in range(1,12) ]

    golayCode = codes.GolayCode(GF(2), extended=False)
    C_basis = list( golayCode.generator_matrix() )
    G = coset_graph(2,C_basis, U_basis)
    G.name("Binary Golay code graph")
    return G

def truncated_binary_Golay_code_graph():
    # e(i) creates the vector e_i
    def e(const int i):
        v = [0]*22
        v[i-1] = 1
        return vector(GF(2),v)
    
    U_basis = [ e(i) for i in range(1,11) ]


    golayCode = codes.GolayCode(GF(2), extended=False)
    C_basis = list( golayCode.generator_matrix() )
    C_basis = list( map( lambda v : v[1:], C_basis) ) #truncate the code
    
    G = coset_graph(2,C_basis, U_basis)
    G.name("Truncated binary Golay code graph")
    return G

def doubly_truncated_binary_Golay_code_graph():
    # e(i) creates the vector e_i
    def e(const int i):
        v = [0]*21
        v[i-1] = 1
        return vector(GF(2),v)
    
    U_basis = [ e(i) for i in range(1,10) ]


    golayCode = codes.GolayCode(GF(2), extended=False)
    C_basis = list( golayCode.generator_matrix() )
    C_basis = list( map( lambda v : v[2:], C_basis) ) #truncate the code
    
    G = coset_graph(2,C_basis, U_basis)
    G.name("Doubly truncated binary Golay code graph")
    return G

def distance_3_doubly_truncated_Golay_code_graph():
    r"""
    we have the subgraph $\Gamma_3(v)$
    """
    G = doubly_truncated_binary_Golay_code_graph()
    v = G.vertices()[0]
    it = G.breadth_first_search(v, distance=3, report_distance=True)
    vertices = []
    for (w,d) in it:
        if d == 3: vertices.append(w)

    # now we have the vertices
    edges =[] 
    n = len(vertices)
    for i in range(n):
        a = vertices[i]
        for j in range(i+1,n):
            b = vertices[j]
            if G.has_edge( (a,b) ): edges.append((a,b))

    H = Graph(edges, format='list_of_edges')
    return H

def shortened_binary_Golay_code_graph():

    def e(const int i):
        v = [0]*22
        v[i-1] = 1
        return vector(GF(2), v)
    
    code = codes.GolayCode(GF(2), False)
    C_basis = list( code.generator_matrix())

    #now shortening
    C_basis = C_basis[1:]
    C_basis = list( map( lambda x: x[1:], C_basis) )

    U_basis = [ e(i) for i in range(1,12) ]

    G = coset_graph(2,C_basis, U_basis)
    G.name("Shortened binary Golay code")
    return G

def shortened_ternary_Golay_code_graph():
    def e(const int i):
        v = [0]*10
        v[i-1] = 1
        return vector(GF(3), v)
    
    code = codes.GolayCode(GF(3), False)
    C_basis = list( code.generator_matrix())

    #now shortening
    C_basis = C_basis[1:]
    C_basis = list( map( lambda x: x[1:], C_basis) )

    U_basis = [ e(i) for i in range(1,6) ]

    G = coset_graph(3,C_basis, U_basis)
    G.name("Shortened ternary Golay code")
    return G

def shortened_extended_ternary_Golay_code_graph():
    def e(const int i):
        v = [0]*11
        v[i-1] = 1
        return vector(GF(3), v)
    
    code = codes.GolayCode(GF(3), True)
    C_basis = list( code.generator_matrix())

    #now shortening
    C_basis = C_basis[1:]
    C_basis = list( map( lambda x: x[1:], C_basis) )

    U_basis = [ e(i) for i in range(1,7) ]

    G = coset_graph(3,C_basis, U_basis)
    G.name("Shortened extended ternary Golay code")
    return G

def shortened_00_11_binary_Golay_code_graph():
    r"""
    C = all words of binary Golay code that start with 00 or 11, and remove the first 2 positions
    """

    def e(const int i):
        v = [0]*21
        v[i-1] = 1
        return vector(GF(2), v)
    
    code = codes.GolayCode(GF(2), False)
    C_basis = list( code.generator_matrix())

    #now shortening
    v = C_basis[0] + C_basis[1] # v has 11 at the start
    C_basis = C_basis[2:]
    C_basis.append(v)
    C_basis = list( map( lambda x: x[2:], C_basis) )

    U_basis = [ e(i) for i in range(1,11) ]

    G = coset_graph(2,C_basis, U_basis)
    G.name("Shortened 00 11 binary Golay code")
    return G

def shortened_000_111_extended_binary_Golay_code_graph():
    r"""
    C = all words of extended binary Golay code that start with 000 or 111, and remove the first 3 positions
    """

    def e(const int i):
        v = [0]*21
        v[i-1] = 1
        return vector(GF(2), v)
    
    code = codes.GolayCode(GF(2))
    C_basis = list( code.generator_matrix())

    #now shortening
    v = C_basis[0] + C_basis[1]+C_basis[2] # v has 111 at the start
    C_basis = C_basis[3:]
    C_basis.append(v)
    C_basis = list( map( lambda x: x[3:], C_basis) )

    U_basis = [ e(i) for i in range(1,13) if i != 10 ]#this time U_basis is a bit different

    G = coset_graph(2,C_basis, U_basis)
    G.name("Shortened 000 111 extended binary Golay code")
    return G

def LintSchrijver_graph():
    def e(const int i):
        v = [0]*6
        v[i] = 1
        return vector(GF(3), v)

    one = vector(GF(3), [1]*6)
    C_basis = [one]
    U_basis = [e(i) for i in range(5)]
    G = coset_graph(3,C_basis,U_basis)

    vertices = set()
    for v in G.vertices():
        v = vector(GF(3), v)
        i = v.dot_product(one)
        v = tuple(v)
        if i in {1,2}:
            vertices.add(v)

    edges = []
    for v in vertices:
        for w in vertices:
            if G.has_edge( (v,w) ):
                edges.append( (v,w) )

    H = Graph(edges,format='list_of_edges')
    H.name("Linst-Schrijver graph")
    return H



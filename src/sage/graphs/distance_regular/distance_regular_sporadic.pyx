# -*- coding: utf-8 -*-
from sage.libs.gap.libgap import libgap
from sage.rings.number_field.number_field import CyclotomicField
from sage.graphs.graph import Graph
from sage.modules.free_module import VectorSpace
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.integer cimport Integer
from sage.modules.free_module_element import vector
import numpy as np
from sage.combinat.integer_vector import IntegerVectors
from sage.matrix.constructor import Matrix
from sage.graphs.graph_generators import GraphGenerators
from sage.coding import codes_catalog as codes

from sage.graphs.distance_regular_codegraphs import coset_graph

def _hamming_weight( codeword ):
    cdef int weight = 0
    for i in codeword:
        if i != 0: weight += 1
        
    return weight

def _codewords_have_different_support( vec1, vec2 ):
   # the support of a codeword is the set of coordinates where the codeword
   # has non-zero entries
   for (i,j) in zip(vec1,vec2):
      if i*j != 0:
         return False
   return True


r"""
include all sporadic (not part of a family) distance regular graphs
"""

def cocliques_HoffmannSingleton():
    from sage.graphs.cliquer import all_max_clique
    D = GraphGenerators.HoffmanSingletonGraph()
    DC = D.complement()

    cocliques = all_max_clique(DC)#100 of this

    edges = []
    for i in range(100):
        sC = frozenset(cocliques[i])
        for j in range(i+1,100):
            if len(sC.intersection(cocliques[j])) == 8:
                sC2 = frozenset(cocliques[j])
                edges.append( (sC,sC2) )

    G = Graph(edges,format="list_of_edges")
    return G

def locally_GQ42_graph():
   H = libgap.AtlasGroup("3^2.U4(3).D8")
   Ns = H.NormalSubgroups()
   group = libgap.Action(Ns[6], Ns[6].Orbit(1))
   G = Graph(group.Orbit([1,9],libgap.OnSets), format='list_of_edges')
   G.name("locally GQ(4,2) graph")
   return G

def ConwaySmith_for_3S7():

    F = CyclotomicField(3)
    w = F.gen()
    
    V= VectorSpace(GF(4), 6)
    z2 = GF(4)('z2') # GF(4) = {0,1,z2, z2+1}

    W = V.span( [(0,0,1,1,1,1), (0,1,0,1,z2,z2+1), (1,0,0,1,z2+1,z2)] )
    # we only need the 45 vectors with 2 zero entries
    # we also embed everything into CC

    K = []
    for v in W:

        #check zero entries
        zeros = 0
        for x in v:
            if x == 0:
                zeros += 1

        if zeros == 2:
            #send to F and in K
            #z2 -> w
            #z2+1 -> w^2
            
            vv = [] #new vector
            for x in v:
                if x == z2:
                    vv.append(w)
                elif x == z2+1:
                    vv.append(w**2)
                else:
                    vv.append( Integer(x) )#this is weirdly needed for some reason

            #now vv is the new vector in F
            vv = vector( F, vv)
            K.append(vv)
            
    #here K is the vectors we need and also in F

    #we need to add other vectors
    for i in range(6):

        #create e_i
        ei = [0]*6
        ei[i] = 1
        ei = vector(F,ei)

        K.append( 2*ei )
        K.append( 2*w*ei )
        K.append( 2*w**2*ei )

    #now K is all the 63 vertices

    def has_edge(u,v):
        com = 0
        for i in range(6):
            com += u[i].conjugate() * v[i]

        if com == 2:
            return True
        return False

    
    G = Graph()
    
    length = len(K)
    for i in range(length):
        K[i].set_immutable()
        for j in range(i+1, length):
            if has_edge(K[i], K[j]):
                K[j].set_immutable()
                G.add_edge( (K[i], K[j]) )

    G.name("Conway-Smith graph for 3S7")
    return G

def graph_3O73():
    group = libgap.AtlasGroup("3.O7(3)",libgap.NrMovedPoints,1134)
    G = Graph( group.Orbit([1,3], libgap.OnSets), format='list_of_edges')
    G.name("Distance transitive graph with automorphism group 3.O_7(3)")
    return G

def Foster_graph_3S6():

    a = libgap.eval("(2,6)(3,5)(4,11)(7,17)(8,16)(9,14)(13,22)(15,25)(18,29)(19,28)(20,21)(24,30)(26,35)(27,33)(31,39)(34,38)(36,43)(37,40)(42,44)")
    b = libgap.eval("(1,2,7,12,4)(3,8,18,20,10)(5,9,19,21,11)(6,13,17,26,15)(14,23,28,31,24)(16,22,29,36,27)(25,32,35,42,34)(30,37,39,44,38)(33,40,43,45,41)")
    group = libgap.Group(a,b)

    G = Graph(group.Orbit( [1,7], libgap.OnSets), format='list_of_edges')
    G.name("Foster graph for 3.Sym(6) graph")

    return G

def J2_graph():

    group = libgap.AtlasGroup("J2", libgap.NrMovedPoints, 315)
    G = Graph( group.Orbit([1,9], libgap.OnSets), format='list_of_edges')
    G.name("J_2 graph")
    return G
    

def Coxeter_graph():
    #construct Fano plane
    points = [ i for i in range(7) ]
    lines = [ frozenset({0,1,2}), frozenset({0,4,5}), frozenset({0,3,6}), frozenset({1,4,6}), frozenset({1,3,5}), frozenset({2,3,4}), frozenset({2,5,6}) ]

    vertices = []
    for p in points:
        for l in lines:
            if p not in l:            
                vertices.append( (p,l) )

    G = Graph()
    pointsSet = set(points)
    for (p,l) in vertices:
        for (q,m) in vertices:
            s = set(l.union(m))
            s.add(p)
            s.add(q)
            if s == pointsSet:
                G.add_edge( ((p,l), (q,m)) )

    G.name("Coxeter graph")
    return G

def IvanovIvanovFaradjev_graph():
    r"""
    requires gap and gap_packages

    """

    libgap.eval("SetInfoLevel(InfoWarning,0)") # silence #I warnings from GAP (without IO pkg)
    libgap.LoadPackage("AtlasRep")

    group = libgap.AtlasGroup("3.M22",libgap.NrMovedPoints,990)
    
    libgap.eval("SetInfoLevel(InfoWarning,1)") # restore #I warnings

    graph = Graph(group.Orbit([1,22],libgap.OnSets), format='list_of_edges')
    
    graph.name("Ivanov-Ivanov-Faradjev Graph")
        
    return graph

def large_Witt_graph():
    r"""
    Return the large Witt graph.

    This builds the large Witt graph. Each vertex represents a codeword.

    EXAMPLES:

        sage: g = large_Witt_graph()
        sage: g.is_distance_regular()
        True

    TESTS::

    """
    # G is the generator matrix of the extended binary Goolay code
    G = np.array([ [1,0,0,0,0,0,0,0,0,0,0,0, 1,0,0,1,1,1,1,1,0,0,0,1],
                   [0,1,0,0,0,0,0,0,0,0,0,0, 0,1,0,0,1,1,1,1,1,0,1,0],
                   [0,0,1,0,0,0,0,0,0,0,0,0, 0,0,1,0,0,1,1,1,1,1,0,1],
                   [0,0,0,1,0,0,0,0,0,0,0,0, 1,0,0,1,0,0,1,1,1,1,1,0],
                   [0,0,0,0,1,0,0,0,0,0,0,0, 1,1,0,0,1,0,0,1,1,1,0,1],
                   [0,0,0,0,0,1,0,0,0,0,0,0, 1,1,1,0,0,1,0,0,1,1,1,0],
                   [0,0,0,0,0,0,1,0,0,0,0,0, 1,1,1,1,0,0,1,0,0,1,0,1],
                   [0,0,0,0,0,0,0,1,0,0,0,0, 1,1,1,1,1,0,0,1,0,0,1,0],
                   [0,0,0,0,0,0,0,0,1,0,0,0, 0,1,1,1,1,1,0,0,1,0,0,1],
                   [0,0,0,0,0,0,0,0,0,1,0,0, 0,0,1,1,1,1,1,0,0,1,1,0],
                   [0,0,0,0,0,0,0,0,0,0,1,0, 0,1,0,1,0,1,0,1,0,1,1,1],
                   [0,0,0,0,0,0,0,0,0,0,0,1, 1,0,1,0,1,0,1,0,1,0,1,1] ])
    
    # condtruction is here: http://mathworld.wolfram.com/LargeWittGraph.html
    
    vertices=[]
    # we will add tuples as vertices via add_vertex(tuple([1,0,1....]))
    cdef int vertices_found = 0 #max is 759
    for vec in IntegerVectors(k=12,max_part=1): #iterate over all binary vectors of size 12
        codeword = np.matmul(vec,G) % 2
        if (_hamming_weight(codeword) == 8 ): # is a valid vertex
            vertices.append(tuple(codeword))
            vertices_found += 1
            if vertices_found == 759: break

    edges = []
    # here W contains all 759 vertices
    for v in vertices:
        for w in vertices:
            # check if w,v are orthogonal and if so, add edge
            if _codewords_have_different_support(v,w):
                edges.append((v,w))

    W = Graph(edges, format='list_of_edges')
    W.name("Large Witt graph")
    return W

def truncated_Witt_graph():
    r"""
    Return the truncated Witt graph.

    This builds the large Witt graph, then removes
    all vertices whose codeword start with a 1.

    EXAMPLES:

        sage: g = large_Witt_graph()
        sage: g.is_distance_regular()
        True

    TESTS::

        sage: g = large_Witt_graph()
        ...
    """
    # get large witt graph and remove all vertices which start with a 1
    G = large_Witt_graph()
    G.delete_vertices(filter( lambda x : x[0] == 1, G.vertices() ))
    G.relabel( lambda v: v[1:] )

    G.name("Truncated Witt graph")
    return G

def doubly_truncated_Witt_graph():

    G = truncated_Witt_graph() 
    G.delete_vertices(filter( lambda x : x[0] == 1, G.vertices() ))
    G.relabel( lambda v: v[1:] )

    G.name("Doubly Truncated Witt graph")
    return G


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

def Leonard_graph():
    from sage.combinat.matrices.hadamard_matrix import hadamard_matrix
    from sage.graphs.cliquer import all_max_clique

    M = hadamard_matrix(12)
    edges = []
    for i in range(12):
        for j in range(12):
            for k in range(12):
                if i == k: continue
                for l in range(12):
                    if j == l: continue
                    if M[i,j]*M[i,l]*M[k,j]*M[k,l] == -1:
                        edges.append( ( (i,j),(k,l) ) )

    D = Graph(edges,format="list_of_edges")
    cls = all_max_clique(D)

    edges = []
    for cl in cls:
        scl = frozenset(cl)
        for p in cl:
            edges.append( (p,scl) )

    G = Graph(edges,format="list_of_edges")
    return G
    

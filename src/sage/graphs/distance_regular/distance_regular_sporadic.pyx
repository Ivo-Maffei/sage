from sage.libs.gap.libgap import libgap
from sage.rings.number_field.number_field import CyclotomicField
from sage.graphs.graph import Graph
from sage.modules.free_module import VectorSpace
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.rings.integer cimport Integer
from sage.modules.free_module_element import vector
import numpy as np
from sage.combinat.integer_vector import IntegerVectors

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


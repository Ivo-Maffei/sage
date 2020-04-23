r"""
all dist reg graphs with unbounded order
"""

from sage.rings.finite_rings.finite_field_constructor import GF
from sage.modules.free_module import VectorSpace
from sage.graphs.graph import Graph
from sage.combinat.designs import design_catalog as Sage_Designs
from sage.graphs.strongly_regular_db import strongly_regular_graph
from sage.arith.misc import is_prime_power
from sage.modules.free_module_element import vector
from sage.libs.gap.libgap import libgap

from distance_regular.utils import *

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

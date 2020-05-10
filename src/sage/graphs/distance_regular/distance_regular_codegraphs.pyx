# cython: profile=False
# -*- coding: utf-8 -*-
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.modules.free_module import VectorSpace
from sage.matrix.constructor import Matrix
from sage.modules.free_module_element import vector
from sage.graphs.graph import Graph

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




# cython: profile=False
# -*- coding: utf-8 -*-
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.modules.free_module import VectorSpace
from sage.matrix.constructor import Matrix
from sage.modules.free_module_element import vector
from sage.graphs.graph import Graph

from cysignals.signals cimport sig_check

def coset_graph( const int q, C_basis, U_basis=None, n=None ):
    r"""
    Computes the coset graph $\Gamma(C)$ where $C = \mathrm{Span}(C_basis)$
    
    Inputs: q, C_basis, U_basis=None, n=None

    The elements of C_basis are vectors over $(\mathbb F_q)^n$.
    U_basis must span the complement of $C$

    If n or U_basis are not given, they will be deduced from C_basis.
    So if n or U_basis are not given, then C_basis should not be empty.
    """

    if n == None:
        n = len(C_basis[0])# dim V
    F = GF(q) #base field
    lambdas = [ x for x in F if x != 0 ]#non-zero elements of F

    def e(const int i):
        v = [0]*n
        v[i-1] = 1
        return vector(F,v,immutable=True)
    
    V = VectorSpace(F,n)

    if U_basis is None:
        C = V.span(C_basis)
        Q = V.quotient(C)
        lift = Q.lift_map()#Q -> V
        U_basis = [ lift(v) for v in Q.basis()]
        
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

    Pei = [] #list of P(e_i)
    for i in range(n+1):
        ei = e(i)
        if ei in U:
            Pei.append(ei)
        else:
            a = Ainv * ei
            # get zero vector and sum a[i]u_i to it
            v = vector(F,[0]*n)
            for i in range(len(U_basis)):
                v += a[i]*U_basis[i]
            v.set_immutable()
            Pei.append(v)
            
    lPei = [ l*u for l in lambdas for u in Pei]

    #now we are ready to build all the edges
    edges = []
    for v in vertices:
        v.set_immutable()
        for u in lPei:
            sig_check()
            w = v + u
            w.set_immutable()
            edges.append( (v, w) )

    G = Graph(edges, format='list_of_edges')
    return G


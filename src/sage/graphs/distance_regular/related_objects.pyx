# -*- coding: utf-8 -*-

r"""
combinatorial objects used for the distance_regular graphs
"""

from sage.matrix.constructor import Matrix
from sage.rings.finite_rings.finite_field_constructor import GF
from sage.arith.misc import is_prime_power
from sage.modules.free_module import VectorSpace
from sage.modules.free_module_element import vector
from sage.libs.gap.libgap import libgap
from sage.rings.integer cimport Integer
from sage.combinat.designs.incidence_structures import IncidenceStructure

from cysignals.signals cimport sig_check

from sage.misc.unknown import Unknown

#ASSOCIATION SCHEMES
class AssociationScheme:

    def _is_association_scheme(self):

        #check matrix size
        if self._matrix.ncols() != self._nX:
            raise ValueError("matrix has wrong size")
        
        #check R0
        for i in range(self._nX):
            if self._matrix[i][i] != 0:
                raise ValueError("identity is not R_0")
            
        
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
                            raise ValueError("failed p{}{}{} (={}) with pair ({},{})".format(i,j,k,pijk,x,y))
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
            self._is_association_scheme()
            

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
    
    def R(self,k):
        Rk = set()
        for i in range(self._nX):
            for j in range(i,self._nX):
                if self._matrix[i][j] == k:
                    Rk.add((self._X[i],self._X[j]))
                    Rk.add((self._X[j],self._X[i]))

        return Rk

    def p(self,i,j,k):
        if self._P[i][j][k] is not None: return self._P[i][j][k]

        nX = self._nX

        self._P[i][j][k] = 0
        found = False
        for x in range(nX):
            for y in range(nX):
                if self._matrix[x][y] == k:
                    found = True
                    break
            if found:
                break

        if self._matrix[x][y] != k:
            raise RuntimeError("something bad happend in code")

        #now (x,y) in R_k
        for z in range(nX):
            if self._matrix[x][z] == i and self._matrix[z][y] == j:
                self._P[i][j][k] += 1

        return self._P[i][j][k]
        

    def compute_intersection_numbers(self):
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


def cyclotomic_scheme(const int q,const int r,check=True):
    #for (q-1)/r even or q power of 2, then the association scheme is symmetric
    #and pseudocyclic
    if r <= 0 or (q-1)%r != 0:
        raise ValueError("we need r to be a (positive) divisor of q-1")

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
                sig_check()
                y = x+z
                relations[XtoInt[x]][XtoInt[y]] = i

    return AssociationScheme(X,relations,check=check)

def distance_regular_association_scheme(const int n, const int r, existence=False, check=True):
    r"""
    Returns an r-class  distance regular association scheme

    We say that an association scheme is distance regular if it is pseudocyclic and
    $p_{i+l mod r, j+l mod r}^{k+l mod r} = p_{i,j}^k for any i,j,k,l \in \{1,...,r\}$
    """
    def result(scheme):
        if check:
            if not scheme.is_pseudocyclic() or scheme.num_classes() != r or scheme.num_points() != n:
                raise RuntimeError("Sage built a wrong association scheme")
        return scheme
    
    if is_prime_power(n) and r > 0 and (n-1)%r == 0 and ( ((n-1)//r)%2 == 0 or n%2 == 0 ):
        #we hve cyclotomic
        if existence: return True
        return result(cyclotomic_scheme(n,r,check))
            
    if existence: return Unknown
    raise RuntimeError("Sage can't build a pseudocyclic association scheme with parameters ({},{})".format(n,r))

def generalised_quadrangle_with_spread(const int s, const int t, existence=False, check=True):
    r"""
    Returns a pair (GQ,S) s.t. GQ is a generalised quadrangle of order (s,t) and S is a spread of GQ
    """
    if s < 1 or t < 1:
        if existence: return False
        raise RuntimeError("No GQ of order ({},{}) exists".format(s,t))

    if s == 1 and t == 1:#we have a square
        if existence: return True
        D = IncidenceStructure([[0,1],[1,2],[2,3],[3,0]])
        return (D,[[0,1],[2,3]])

    if is_prime_power(s) and t == s*s:
        if existence: return True
        (GQ,S) = dual_GQ_ovoid(*generalised_quadrangle_hermitian(s))
        if check:
            if not is_GQ_with_spread(GQ,S,s,t):
                raise RuntimeError("Sage built a wrong GQ with spread")
        return (GQ,S)

    if existence: return Unknown
    raise RuntimeError("Sage can't build a GQ of order ({},{}) with a spread".format(s,t))

def is_GQ_with_spread(GQ,S,const int s, const int t):
    r"""
    Checks if GQ is a generalised quadrangle of order (s,t) and
    checks that S is a spred of GQ
    """
    res = GQ.is_generalised_quadrangle(parameters=True)
    if res is False or res[0] != s or res[1] != t:
        return False

    #check spread
    points = set(GQ.ground_set())
    for line in S:
        if not points.issuperset(line):
            return False
        points = points.difference(line)
        
    if points:
        return False
    
    return True
        
def dual_GQ_ovoid(GQ,O):
    r"""
    Computes the dual of GQ and returns the image of O under the dual map
    """
    #we compute the dual of GQ and of O

    #GQ.ground_set()[i] becomes newBlocks[i]
    #GQ.blocks()[i] becomes i
    newBlocks = [ [] for _ in range(GQ.num_points())]
    pointsToInt = { p: i for i,p in enumerate(GQ.ground_set()) }

    for i,b in enumerate(GQ.blocks()):
        for p in b:
            newBlocks[pointsToInt[p]].append(i)

    S = [ newBlocks[pointsToInt[p]] for p in O]

    D = IncidenceStructure(newBlocks)
    return (D,S)
    
def generalised_quadrangle_hermitian(const int q):
    r"""
    Construct the generalised quadrangle H(3,q^2) with an ovoid
    The GQ has order (q^2,q)
    """

    GU = libgap.GU(4,q)
    H = libgap.InvariantSesquilinearForm(GU)["matrix"]
    Fq = libgap.GF(q*q)
    zero = libgap.Zero(Fq)
    one = libgap.One(Fq)
    V = libgap.FullRowSpace(Fq,4)

    e1 = [one,zero,zero,zero] #isotropic point
    assert( e1*H*e1 == zero, "e1 not isotropic")

    points = list(libgap.Orbit(GU,e1,libgap.OnLines)) #all isotropic points
    pointInt = { x:(i+1) for i,x in enumerate(points) } #+1 because GAP starts at 1
    #points is the hermitian variety

    GUp = libgap.Action(GU, points, libgap.OnLines)#GU as permutation group of points

    e2 = [zero,one,zero,zero]
    #we have totally isotropic line
    line = V.Subspace([e1,e2])
    lineAsPoints = [libgap.Elements(libgap.Basis(b))[0] for b in libgap.Elements(line.Subspaces(1)) ]
    line = libgap.Set([ pointInt[p] for p in lineAsPoints ])

    lines = libgap.Orbit(GUp, line, libgap.OnSets)#all isotropic lines

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
        for i in range(a): aGap += one
        p = [zero,one,one,aGap,zero]
    else:
        a = libgap.PrimitiveRoot(Fq)**(q-1)
        p = [zero,one,a+one,a,zero]
        
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

    D = IncidenceStructure(lines)
    return (D,ovoid)

def extended_Kasami_code(const int s, const int t):
    #check s,t are good
    
    F2 = GF(2)
    V = VectorSpace(F2, s)
    elemsFs = [x for x in GF(s)]

    #we ensure that 0 is the first element of elemsFs
    if not elemsFs[0].is_zero():
        for i in range(s):
            if elemsFs[i].is_zero:
                a = elemsFs[0]
                elemsFs[0] = elemsFs[i]
                elemsFs[i] = a
                break
    
    FsToInt = { x : i for i,x in enumerate(elemsFs)}
    elemsFsT = [x**(t+1) for x in elemsFs]
    FsTToInt = { x: i for i,x in enumerate(elemsFsT)}

    e1 = [0]*s
    e1[0] = 1
    e1 = vector(F2,e1,immutable=True)

    W1_basis = []
    for i in range(s-1):
        v = [0]*s
        v[i] = 1
        v[s-1] = 1
        W1_basis.append(v)
    W1 = V.span(W1_basis) #W1 satisfies \sum v[i] = 0

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
    W2 = V.span(W2_basis) #W2 satisfies \sum v[i]elemsFs[i] = 0


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

def Kasami_code(const int s, const int t):
    r"""
    take extended Kasami and truncate it
    """

    C = extended_Kasami_code(s,t)
    codebook = [v[1:] for v in C.basis()]
    V = VectorSpace(GF(2),s-1)
    
    return V.span(codebook)

def two_graph(const int n,l=None, regular=True, existence=False, check=True):
    from sage.combinat.designs.twographs import taylor_twograph, is_twograph

    def do_check(D):
        if not check: return#check disabled
        if not is_twograph(D):
            raise RuntimeError("Sage built an incorrect two-graph")
        if regular and not D.is_regular_twograph():
            raise RuntimeError("Sage built an incorrect regular two-graph")
        
    if regular and l is None:
        raise ValueError("If two-graph is regular, then specify l value")
    
    if l is not None and not regular:
        raise ValueError("If you want the two-graph to satisfy the l parameter, then pass regular=True")

    if is_prime_power(n-1) and n%2 == 0:
        #possible taylor U_3(q) or its complement
        (p,k) = is_prime_power(n-1,get_data=True)
        if k % 3 == 0:
            q = p**(k//3)
            if regular and l == (q-1)*(q*q+1)//2:#taylor U_3(q)
                if existence: return True
                D = taylor_twograph(q)
                do_check(D)
                return D
            if regular and l == n - 2 - (q-1)*(q*q+1)//2:#complement of above
                if existence: return True
                D = taylor_twograph(q)
                D = D.complement()
                do_check(D)
                return D

    if existence: return Unknown
    if regular:
        raise RuntimeError("Sage doesn't know how to build a regular two-graph with parameters ({},{})".format(n,l))
    raise RuntimeError("Sage doesn't know how to build a two-graph with {} points".format(n))
    

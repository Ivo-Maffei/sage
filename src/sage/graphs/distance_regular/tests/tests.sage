from sage.graphs.distance_regular import *
from sage.graphs.distance_regular import _sporadic_graph_database

from sage.arith.misc import binomial
from sage.combinat.q_analogues import q_binomial
from sage.functions.other import sqrt
from time import time

from sage.parallel.decorate import fork

timeLimit = 1200 #20 min
edgeLimit = 500000
warning = "WARNING!!!!!!!!"
prime_powers = [2,3,4,5,7,8,9,11,13,16,17,19,23,25]
prime_powers_large = prime_powers + [27,29,31,32,37,41,43,47,49,53,59,61,64,67,71,73,79,81,83,89,97]

#@fork(timeout=timeLimit,verbose=False)
def timeout_wrapper(f,*t):
    return f(*t)

def test_sporadic():
    ok = 0
    fail = 0
    for arr in _sporadic_graph_database:
        start = time()
        G = _sporadic_graph_database[arr]()
        end = time()
        if tuple(intersection_array_from_graph(G)) != arr:
            print("{} {} failed".format(warning,arr))
            fail+= 1
        else:
            print("{} success ({} edges in {})".format(arr,G.size(),end-start))
            ok += 1

    return (ok,fail)

def call_wrapper(f,obj,unpack):
    if unpack:
        return f(*obj)
    else:
        return f(obj)

def is_iterable(obj):
    try:
        iter(obj)
    except TypeError:
        return False
    return True

def test_function(name,graph,params,array,edges=None,fromArray=False):

    ok = 0
    fail = 0
    iterable = True #assume true; doesn't matter

    def edgesDefault(arr):
        try:
            nE = arr[0]*number_of_vertices_from_intersection_array(arr) // 2
        except OverflowError:
            return edgeLimit+1
        return nE

    def edgesWrapper(t):
        try:
            nE = call_wrapper(edges,t,iterable)
        except OverflowError:
            return edgeLimit +1
        return nE

    for t in params():#parmas is a generator
        iterable = is_iterable(t)
        if edges is None:
            arr = call_wrapper(array,t,iterable)
            nE = edgesDefault(arr)
            if nE > edgeLimit: continue
        else:
            nE = edgesWrapper(t)
            if nE > edgeLimit: continue
            arr = call_wrapper(array,t,iterable)

        start = time()
        if fromArray:
            G = distance_regular_graph(arr,check=False)
        else:
            G = call_wrapper(graph,t,iterable)
        end = time()
        if type(G) == type(""):#graph not builted because of timeout
            fail += 1
            print("{} with parameters {} and timeout after {}".format(name,t,timeLimit))
        elif intersection_array_from_graph(G) == arr:
            ok += 1
            print("{} with parameters {} success ({} vertices, {} edges in {})".format(name,t,G.order(),G.size(),end-start))
        else:
            fail += 1
            print("{} {} with parameters {} failed".format(warning,name,t))

        #sanity check on edge function
        if edges is not None and type(G) != type("") and nE != G.size():
            print("{} {} edges function is wrong".format(warning,name))

    return (ok,fail)

def dual_polar_orthogonal_params():
    for d in range(3,6):
            for q in prime_powers[:7]:
                yield (0,d,q)
                yield (1,d,q)
                yield (-1,d,q)

def dual_polar_orthogonal_array(e,d,q):
    return intersection_array_from_classical_parameters(d,q,0,q^(1-e))

def double_odd_params():
    for n in range(1,8):#values >= 8 is_distance_regular gives an error
            yield n

def double_odd_array(x):
    k = x+1
    d = 2*x + 1

    cs = [ (i+1) // 2 for i in range(d+1)]
    bs = [ k - cs[i] for i in range(d)]

    return bs+cs[1:]

def double_odd_edges(x):
    return binomial(2*x+1,x)*(x+1)

def bilinear_form_params():
    for d in range(3,10):
        for e in range(d,10):
            for q in prime_powers:
                yield (d,e,q)

def bilinear_form_array(d,e,q):
    return intersection_array_from_classical_parameters(d,q,q-1,q**e-1)

def bilinear_form_edges(d,e,q):
    return q**(d*e)*q_binomial(d,1,q)*(q**e-1) // 2

def alternating_form_params():
    for n in range(6,12):#n<6 => d < 3
        for q in prime_powers:
            yield (n,q)

def alternating_form_array(n,q):
    m = 2 * (n+1)//2 -1
    return intersection_array_from_classical_parameters(n//2,q*q,q*q-1,q**m-1)

def alternating_form_edges(n,q):
    nV = (n-1)*n // 2
    nV = q**nV
    m = 2*(n+1)//2 -1
    k = q_binomial(n//2,1,q)*(q**m-1)
    return k*nV // 2

def hermitian_form_params():
    for n in range(3,10):
        for q in prime_powers:
            yield (n,q*q)

def hermitian_form_array(n,q):
    r = sqrt(q)
    return intersection_array_from_classical_parameters(n, -r, -r-1, -(-r)**n-1)
    
def hermitian_form_edges(n,q):
    r = sqrt(q)
    nV = (n-1)*n // 2
    nV = (q**nV) * (r**n)
    k = q_binomial(n,1,-r)*(-(-r)**n-1)
    return nV*k // 2

def half_cube_params():
    for  n in range(6,50):#smaller n has diameter < 3
        yield n

def half_cube_array(n):
    return intersection_array_from_classical_parameters(n//2,1,2,2*((n+1)//2)-1)

def half_cube_edges(n):
    nV = 2**(n-1)
    k = n-1 + binomial(n-1,2)
    return nV*k//2

def Grassmann_params():
    for e in range(3,7):#diameter is e
        for n in range(2*e,10):
            for q in prime_powers[:5]:#q>7 is too big
                yield (q,n,e)

def Grassmann_array(q,n,e):
    return intersection_array_from_classical_parameters(e,q,q,q_binomial(n-e+1,1,q)-1)

def Grassmann_edges(q,n,e):
    nV = q_binomial(n,e,q)
    k = q_binomial(e,1,q)*(q_binomial(n-e+1,1,q) -1)
    return nV*k//2

def double_Grassmann_params():
    for e in range(1,10):#diameter is 2e+1
        for q in prime_powers[:5]:#to big otherwise
            yield (q,e)

def double_Grassmann_array(q,e):
    d = 2*e +1
    cs = [ q_binomial((i+1)//2,1,q) for i in range(d+1)]
    bs = [ q_binomial(e+1,1,q)-cs[i] for i in range(d)]
    return bs+cs[1:]

def double_Grassmann_edges(q,e):
    nV = 2*q_binomial(2*e+1,e,q)
    k= q_binomial(e+1,1,q)
    return k*nV//2

def hermitian_cover_params():
    for q in prime_powers:
        for r in (q*q -1).divisors()[1:]:#r==1 is complete graph
            if( (r%2 == 1 and (q-1)%r == 0) or
                (q%2 == 0 and (q+1)%r == 0) or
                (q%2 == 1 and ((q+1)//2)%r == 0)):
                yield (q,r)

def hermitian_cover_array(q,r):
    #diameter 3 r cover of K_{q^3+1}
    if r%2 == 1 and (q-1)%r == 0:
        mu = (q**3-1)//r
    else:
        mu = (q+1)*( (q**2-1)//r )
    return [q**3,(r-1)*mu,1,1,mu,q**3]

def hermitian_cover_edges(q,r):
    nV = r*(q**3+1)
    return nV*q**3 // 2

def AB_params():
    for m in range(1,100):#m=0->n=1->graph is not connected
        n = 2*m+1
        yield n

def AB_array(n):
    return [2**n-1, 2**n-2, 2**(n-1)+1, 1, 2, 2**(n-1)-1]

def AB_edges(n):
    nV = 2**(2*n-1)#num vertices // 2
    return nV*(2**n-1)

def Preparata_params():
    for t in range(1,50):
        for i in range(2*t-1):
            yield(t,i)

def Preparata_array(t,i):
    q = 2**(2*t-1)
    p = 2**(i+1)
    return [2*q-1,2*q-p,1,1,p,2*q-1]

def Preparata_edges(t,i):
    q = 2**(2*t-1)
    p = 2**i
    nV = q*(q//p) #n vertices /2
    return nV*(2*q-1)

def Brouwer_Pasechnik_params():
    for q in prime_powers:
        yield q

def Brouwer_Pasechnik_array(q):
    return [q**3-1,q**3-q,q**3-q**2+1,1,q,q**2-1]

def Brouwer_Pasechnik_edges(q):
    nV = q**6
    return nV*(q**3-1)//2

def Pasechnik_params():
    for q in prime_powers:
        yield q

def Pasechnik_array(q):
    return [q**3,q**3-1,q**3-q,q**3-q**2+1,1,q,q**2-1,q**3]

def Pasechnik_edges(q):
    nV = q**6 #num vertices / 2
    return nV*(q**3)

def association_scheme_params():
    #if new association schemes are added
    #this function should be updated
    for q in prime_powers_large:
        for r in (q-1).divisors()[1:]:#avoid r ==1, which is complete graph
            if distance_regular_association_scheme(q,r,existence=True) is True:
                yield(q,r)

def association_scheme_array(q,r):
    mu = (q-1)//r
    return [r*mu+1,(r-1)*mu,1,1,mu,r*mu+1]

def association_scheme_edges(q,r):
    nV = (q+1)*r
    return nV*q // 2

def GQ_graph_params():
    #if new GQ with spread are added
    #this function should be update
    for q in prime_powers:
        yield (q,q*q)

def GQ_graph_array(s,t):
    return [s*t,s*(t-1),1,1,t-1,s*t]

def GQ_graph_edges(s,t):
    return (s+1)*(s*t+1)*s*t // 2

def gen_symplectic_params():
    for m in range(1,50):
        n = 2*m
        for q in prime_powers:
            for r in q.divisors()[1:]:#r==1 we get complete graph
                yield (q,n,r)

def gen_symplectic_array(q,n,r):
    qn = q**n
    return [qn-1,((r-1)*qn)//r,1,1,qn//r,qn-1]

def gen_symplectic_edges(q,n,r):
    nV = q**n * r
    return nV*(q**n-1)//2

def BIBD_graph_params():
    #this is complecated to predict
    #so go wild
    #we do know that graph has v*k edges
    #no trivial cases k<=2 or v == k
    for v in range(4,edgeLimit):
        for k in range(3,v):#k<v is obvious
            l = (k*(k-1))//(v-1)
            if designs.balanced_incomplete_block_design(v,k,lmbd=l,existence=True) is True:
                yield(v,k)

def BIBD_graph_array(v,k):
    l = (k*(k-1))//(v-1)
    return [k,k-1,k-l,1,l,k]

def BIBD_graph_edges(v,k):
    return v*k

def Denniston_arc_params():
    for i in range(1,20):
        n = 2**i
        yield n

def Denniston_arc_array(n):
    return [n*n-n+1, n*(n-1), n*(n-1), n,1,1, (n-1)**2, n*n-n+1]

def Denniston_arc_edges(n):
    return (n*n+1)*(n*n-n+1)**2

def unitary_graph_params():
    for q in prime_powers[1:]: #q>2
        yield q

def unitary_graph_array(q):
    return [q*q-q,q*q-q-2,q+1,1,1,q*q-2*q]

def Taylor_graph_params():
    #if more twographs are implemented
    #this function should change
    for q in prime_powers[1:]: #odd prime
        if q % 2 == 0: continue
        n = q**3+1
        l = (q-1)*(q*q+1)//2
        yield (n,l)
        yield (n, n-2 -l)

def Taylor_graph_array(n,l):
    k = n-1
    mu = k-1-l
    return [k,mu,1,1,mu,k]

def Taylor_graph_edges(n,l):
    return n*(n-1)

def TD_graph_params():
    #wild as for BIBD
    #edges is n^3 l^2
    for n in range(5,100):
        for l in range(1,1000):
            if designs.symmetric_net(n,l,existence=True) is True:
                yield (n,l)

def TD_graph_array(n,l):
    return [n*l,n*l-1,(n-1)*l,1,1,l,n*l-1,n*l]

def TD_graph_edges(n,l):
    nBlocks = n*n*l #which is half of vertices
    return nBlocks*n*l

def gen_dodec_params():
    for q in [2,3,4,5]:
        yield (1,q)
        yield (q,1)

def gen_poly_array(n,s,t):
    d = n//2
    cs = [ 1 for i in range(d) ]
    cs[d-1] = t+1

    k = s*(t+1)
    bs = [k] + [ s*t for i in range(d-1) ]

    return bs+cs

def gen_dodec_array(s,t):
    return gen_poly_array(12,s,t)

def gen_octagon_params():
    
    yield (2,4)
    yield (4,2)
    
    for q in prime_powers:
        if graphs.strongly_regular_graph((q+1)*(q*q+1),q*(q+1),q-1,q+1,existence=True) is True:
            yield (1,q)
            yield (q,1)

def gen_octagon_array(s,t):
    return gen_poly_array(8,s,t)

def gen_hexagon_params():

    #G_2(q)
    yield (2,2)
    yield (3,3)
    yield (4,4)
    yield (5,5)

    #3D4
    yield (2,8)
    yield (8,2)
    yield (3,27)
    yield (27,3)
    
    for q in prime_powers:
        yield (1,q)
        yield (q,1)

def gen_hexagon_array(s,t):
    return gen_poly_array(6,s,t)

def Kasami_params():
    for i in range(1,20):
        q = 2**i
        yield (q*q,q)
        for j in range(10):
            for m in range(1,j+1):
                if gcd(m,2*j+1) == 1:
                    yield (q**(2*j+1), q**m)

def Kasami_array(s,t):
    if s == t*t:
        return [s-1,s-t,1,1,t,s-1]
    else:
        (p,k) = is_prime_power(t,get_data=True)
        (p,h) = is_prime_power(s,get_data=True)
        i = gcd(k,h)
        #i is largest number dividing k and h
        #so m = k//i and 2j+1 = h // i
        q = 2**i
        return [s-1,s-q,(s//q)*(q-1)+1,1,q,(s//q)-1]

def Kasami_edges(s,t):
    if s == t*t:
        return (s*t)//2 * (s-1)
    else:
        return s*s//2 * (s-1)

def extended_Kasami_array(s,t):
    if s == t*t:
        return [s,s-1,s-t,1,1,t,s-1,s]
    else:
        (p,k) = is_prime_power(t,get_data=True)
        (p,h) = is_prime_power(s,get_data=True)
        i = gcd(h,k)
        q = 2**i
        return [s,s-1,s-q,(s//q)*(q-1)+1,1,q,(s//q)-1,s]

def extended_Kasami_edges(s,t):
    if s == t*t:
        return s*t*s
    else:
        return s*s*s
        
    
_tests_list = [
    #("sporadic graphs",test_sporadic),
    #("orthogonal dual polar",dual_polar_orthogonal,dual_polar_orthogonal_params,dual_polar_orthogonal_array),
    #("double odd", double_odd_graph, double_odd_params, double_odd_array, double_odd_edges),
    #("bilinear form graph",bilinear_form_graph,bilinear_form_params,bilinear_form_array,bilinear_form_edges),
    #("alternating form graph",alternating_form_graph,alternating_form_params,alternating_form_array,alternating_form_edges), #to test
    #("hermitian form graph",hermitian_form_graph,hermitian_form_params,hermitian_form_array,hermitian_form_edges),
    #("half cube",half_cube,half_cube_params,half_cube_array,half_cube_edges),
    #("Grassmann",Grassmann_graph,Grassmann_params,Grassmann_array,Grassmann_edges),
    #("double Grassmann",double_Grassmann_graph,double_Grassmann_params,double_Grassmann_array,double_Grassmann_edges),
    #("hermitian cover",hermitian_cover,hermitian_cover_params,hermitian_cover_array,hermitian_cover_edges),
    #("AB graph",AB_graph,AB_params,AB_array,AB_edges),
    #("Preparata graph", Preparata_graph,Preparata_params,Preparata_array,Preparata_edges),
    #("Brouwer Pasechnik graph",Brouwer_Pasechnik_graph,Brouwer_Pasechnik_params,Brouwer_Pasechnik_array,Brouwer_Pasechnik_edges),
    #("Pasechnik graph",Pasechnik_graph,Pasechnik_params,Pasechnik_array,Pasechnik_edges),
    #("Association scheme graph",graph_from_association_scheme, association_scheme_params ,association_scheme_array, association_scheme_edges), #test primes > 100 and error in drg for (13,2)
    #("GQ graphs",graph_from_GQ_spread, GQ_graph_params,GQ_graph_array,GQ_graph_edges),
    #("Symplectic cover", symplectic_cover, gen_symplectic_params, gen_symplectic_array, gen_symplectic_edges),
    #("BIBD graph", graph_from_square_BIBD, BIBD_graph_params, BIBD_graph_array, BIBD_graph_edges), #to test big ones
    #("Denniston graph", graph_from_Denniston_arc, Denniston_arc_params, Denniston_arc_array, Denniston_arc_edges),
    #("unitary nonisotropic graph",unitary_nonisotropic_graph, unitary_graph_params, unitary_graph_array),
    #("Taylor graph",Taylor_graph, Taylor_graph_params, Taylor_graph_array, Taylor_graph_edges),
    ("TD graph",graph_from_TD,TD_graph_params,TD_graph_array,TD_graph_edges),
    #("Generalised dodecagon",generalised_dodecagon, gen_dodec_params,gen_dodec_array),
    #("Generalised octagon",generalised_octagon, gen_octagon_params,gen_octagon_array),
    ("Generalised hexagon", generalised_hexagon, gen_hexagon_params, gen_hexagon_array),
    ("Kasami graph",Kasami_graph,Kasami_params,Kasami_array,Kasami_edges),
    ("Extended Kasami graph",extended_Kasami_graph,Kasami_params,extended_Kasami_array,extended_Kasami_edges),
]

def test_all(fromArray=False):
    totalOK = 0
    totalFail = 0

    for t in _tests_list:
        name = t[0]
        print("start testing {}".format(name))
        
        lt = len(t)
        if lt == 2:
            (ok,fail) = t[1]()
        else:
            graph = t[1]
            params = t[2]
            array = t[3]
            edges = None if lt == 4 else t[4]
            res = timeout_wrapper(test_function,name,graph,params,array,edges,fromArray)
            if type(res) == type(""):
                print("timeout..., not counting")
                (ok,fail) = (0,0)
            else:
                (ok,fail) = res
    
        totalOK += ok
        totalFail += fail
        print("{} terminated: fail {}, ok {}, total {}".format(name,fail,ok,ok+fail))
        print("-------------------------------------------------------")

    print("All functions tested")
    print("Tests passed {}, failed {}, total {}".format(totalOK, totalFail, totalOK+totalFail))


def test_random_array(n, drange, maxV , noConstraints=False):
    #we generate n random arrays
    #they should have diameter in drange
    #each entry in the array is <= maxV (use to bound the graph size)
    #size of graph is < maxV * (maxV^d-1)/(maxV-1) / 2
    #if noConstraints is True, then arrays are completely random
    #otherwise we ensure c_1 =1 and c[i] <= c[i+1]
    #and b[i] >= b[i+1] and a_i >=0
    from numpy.random import randint
    D = len(drange)
    ds = randint(0,D,n)

    for v in range(n):
        d = drange[ds[v]]
        if noConstraints:
            arr = list(randint(1,maxV,2*d))
        else:
            bs = [randint(1,maxV-1)]#we will increase b_0 by 1 later to ensure b_i < b_0
            for i in range(d-1):
                bs.append(randint(1,bs[i]+1))
            
            bs[0] += 1
            bs.append(0)#we need b_d = 0 for below
            cs = [1]
            for i in range(d-1):
                cs.append(randint(cs[i],bs[0]-bs[i+2]+1))

            arr = bs[:-1]+cs
        print("testing array {}".format(arr))
        if distance_regular_graph(arr,existence=True) is True:
            print("array is good!")
            n = number_of_vertices_from_intersection_array(arr)
            if n*arr[0] > 2*edgeLimit:
                print("too big")
                continue
            G = distance_regular_graph(arr,check=True)
            print("constructed {}".format(G.name()))
                
    print("tests terminated")
            
test_all()
#test_random_array(60,[3,4,5,6],30)

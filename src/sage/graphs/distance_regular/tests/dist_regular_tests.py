from sage.graphs.distance_regular import *

def test_graphs(arr):
    r"""

    TESTS::
    
        #diameter 8
        sage: arr = [3,2,2,2,2,1,1,1,1,1,1,1,2,2,2,3]; test_graphs(arr)
        True

        sage: arr = [7,6,4,4,4,1,1,1,1,1,1,2,4,4,6,7]; test_graphs(arr)
        True

        sage: arr = [8,7,6,5,4,3,2,1,1,2,3,4,5,6,7,8]; test_graphs(arr)
        True

        #diameter 7
        sage: arr = [3,2,2,2,1,1,1,1,1,1,1,1,1,3]; test_graphs(arr)
        True

        sage: arr = [14,12,10,8,6,4,2,1,2,3,4,5,6,7]; test_graphs(arr)
        True
    
        sage: arr = [49,36,25,16,9,4,1,1,4,9,16,25,36,49]; test_graphs(arr)
        True

        sage: arr = [4,3,3,2,2,1,1,1,1,2,2,3,3,4]; test_graphs(arr)
        True

        sage: arr = [7,6,5,4,3,2,1,1,2,3,4,5,6,7]; test_graphs(arr)
        True

        sage: arr = [22,21,20,16,6,2,1,1,2,6,16,20,21,22]; test_graphs(arr)
        True

        sage: arr = [23,22,21,20,3,2,1,1,2,3,20,21,22,23]; test_graphs(arr)
        True

        #diameter 6
        sage: arr = [4,2,2,2,2,2,1,1,1,1,1,2]; test_graphs(arr)
        True

        sage: arr = [6,3,3,3,3,3,1,1,1,1,1,2]; test_graphs(arr)
        True

        sage: arr = [7,6,6,5,5,4,1,1,2,2,3,3]; test_graphs(arr)
        True

        sage: arr = [12,10,8,6,4,2,1,2,3,4,5,6]; test_graphs(arr)
        True

        sage: arr = [13,12,11,10,9,8,1,2,3,4,5,6]; test_graphs(arr)
        True

        sage: arr = [18,15,12,9,6,3,1,2,3,4,5,6]; test_graphs(arr)
        True

        sage: arr = [42,30,20,12,6,2,1,4,9,16,25,36]; test_graphs(arr)
        True

        sage: arr = [48,35,24,15,8,3,1,4,9,16,25,36]; test_graphs(arr)
        True

        sage: arr = [78,55,36,21,10,3,1,6,15,28,45,66]; test_graphs(arr)
        True

        sage: arr = [21,20,16,6,2,1,1,2,6,16,20,21]; test_graphs(arr)
        True

        sage: arr = [21,20,16,9,2,1,1,2,3,16,20,21]; test_graphs(arr)
        True

        sage: arr = [22,21,20,3,2,1,1,2,3,20,21,22]; test_graphs(arr)
        True

        sage: arr = [36,25,16,9,4,1,1,4,9,16,25,36]; test_graphs(arr)
        True

        sage: arr = [66,45,28,15,6,1,1,6,15,28,45,66]; test_graphs(arr)
        True

        sage: arr = [3,2,2,2,2,2,1,1,1,1,1,3]; test_graphs(arr)
        True

        sage: arr = [4,3,3,3,3,3,1,1,1,1,1,4]; test_graphs(arr)
        True

        sage: arr = [5,4,4,4,4,4,1,1,1,1,1,5]; test_graphs(arr)
        True

        sage: arr = [12,11,10,9,8,7,1,2,3,4,5,12]; test_graphs(arr)
        True

        sage: arr = [6,5,4,3,2,1,1,2,3,4,5,6]; test_graphs(arr)
        True

        #diameter 5
        sage: arr = [6,5,5,4,4,1,1,2,2,3]; test_graphs(arr)
        True

        sage: arr = [10,8,6,4,2,1,2,3,4,5]; test_graphs(arr)
        True

        sage: arr = [11,10,9,8,7,1,2,3,4,5]; test_graphs(arr)
        True

        sage: arr = [15,12,9,6,3,1,2,3,4,5]; test_graphs(arr)
        True

        sage: arr = [20,16,12,8,4,1,2,3,4,5]; test_graphs(arr)
        True

        sage: arr = [30,20,12,6,2,1,4,9,16,25]; test_graphs(arr)
        True

        sage: arr = [35,24,15,8,3,1,4,9,16,25]; test_graphs(arr)
        True

        sage: arr = [40,28,18,10,4,1,4,9,16,25]; test_graphs(arr)
        True

        sage: arr = [45,32,21,12,5,1,4,9,16,25]; test_graphs(arr)
        True

        sage: arr = [50,36,24,14,6,1,4,9,16,25]; test_graphs(arr)
        True

        sage: arr = [55,36,21,10,3,1,6,15,28,45]; test_graphs(arr)
        True

        sage: arr = [3,2,1,1,1,1,1,1,2,3]; test_graphs(arr)
        True

        sage: arr = [22,20,18,2,1,1,2,9,20,22]; test_graphs(arr)
        True

        sage: arr = [25,16,9,4,1,1,4,9,16,25]; test_graphs(arr)
        True

        sage: arr = [45,28,15,6,1,1,6,15,28,45]; test_graphs(arr)
        True

        sage: arr = [7,6,6,4,4,1,1,3,3,7]; test_graphs(arr)
        True

        sage: arr = [10,9,8,7,6,1,2,3,4,10]; test_graphs(arr)
        True

        sage: arr = [13,12,12,9,9,1,1,4,4,13]; test_graphs(arr)
        True

        sage: arr = [3,2,2,1,1,1,1,2,2,3]; test_graphs(arr)
        True

        sage: arr = [5,4,3,2,1,1,2,3,4,5]; test_graphs(arr)
        True

        sage: arr = [7,6,6,1,1,1,1,6,6,7]; test_graphs(arr) 
        True

        sage: arr = [10,9,8,2,1,1,2,8,9,10]; test_graphs(arr)
        True

        sage: arr = [16,15,12,4,1,1,4,12,15,16]; test_graphs(arr)
        True

        sage: arr = [22,21,16,6,1,1,6,16,21,22]; test_graphs(arr)
        True

        #diameter 4
        sage: arr = [3,2,2,1,1,1,1,2]; test_graphs(arr)
        True

        sage: arr = [4,2,2,2,1,1,1,2]; test_graphs(arr)
        True

        sage: arr = [5,4,4,3,1,1,2,2]; test_graphs(arr)
        True

        sage: arr = [6,3,3,3,1,1,1,2]; test_graphs(arr)
        True

        sage: arr = [7,6,4,4,1,1,1,6]; test_graphs(arr)
        True

        sage: arr = [8,4,4,4,1,1,1,2]; test_graphs(arr)
        True

        sage: arr = [8,6,4,2,1,2,3,4]; test_graphs(arr)
        True

        sage: arr = [9,8,6,3,1,1,3,8]; test_graphs(arr)
        True

        sage: arr = [9,8,7,6,1,2,3,4]; test_graphs(arr)
        True

        sage: arr = [10,5,5,5,1,1,1,2]; test_graphs(arr)
        True

        sage: arr = [10,8,8,2,1,1,4,5]; test_graphs(arr)
        True

        sage: arr = [10,8,8,8,1,1,1,5]; test_graphs(arr)
        True

        sage: arr = [11,10,6,1,1,1,5,11]; test_graphs(arr)
        True

        sage: arr = [12,8,8,8,1,1,1,3]; test_graphs(arr)
        True

        sage: arr = [12,9,6,3,1,2,3,4]; test_graphs(arr)
        True

        sage: arr = [14,7,7,7,1,1,1,2]; test_graphs(arr)
        True

        sage: arr = [16,12,8,4,1,2,3,4]; test_graphs(arr)
        True

        sage: arr = [20,12,6,2,1,4,9,16]; test_graphs(arr)
        True

        sage: arr = [20,15,10,5,1,2,3,4]; test_graphs(arr)
        True

        sage: arr = [24,15,8,3,1,4,9,16]; test_graphs(arr)
        True

        sage: arr = [24,18,12,6,1,2,3,4]; test_graphs(arr)
        True

        sage: arr = [28,18,10,4,1,4,9,16]; test_graphs(arr)
        True

        sage: arr = [28,21,14,7,1,2,3,4]; test_graphs(arr)
        True

        sage: arr = [30,28,24,16,1,3,7,15]; test_graphs(arr)
        True

        sage: arr = [32,21,12,5,1,4,9,16]; test_graphs(arr)
        True

        sage: arr = [36,21,10,3,1,6,15,28]; test_graphs(arr)
        True

        sage: arr = [36,24,14,6,1,4,9,16]; test_graphs(arr)
        True

        sage: arr = [40,27,16,7,1,4,9,16]; test_graphs(arr)
        True

        sage: arr = [44,30,18,8,1,4,9,16]; test_graphs(arr)
        True

        sage: arr = [48,33,20,9,1,4,9,16]; test_graphs(arr)
        True

        sage: arr = [52,36,22,10,1,4,9,16]; test_graphs(arr)
        True

        sage: arr = [56,39,24,11,1,4,9,16]; test_graphs(arr)
        True

        sage: arr = [60,42,26,12,1,4,9,16]; test_graphs(arr)
        True

        sage: arr = [5,4,1,1,1,1,4,5]; test_graphs(arr)
        True

        sage: arr = [6,4,2,1,1,1,4,6]; test_graphs(arr)
        True

        sage: arr = [10,6,4,1,1,2,6,10]; test_graphs(arr)
        True

        sage: arr = [16,9,4,1,1,4,9,16]; test_graphs(arr)
        True

        sage: arr = [20,18,4,1,1,2,18,20]; test_graphs(arr)
        True

        sage: arr = [28,15,6,1,1,6,15,28]; test_graphs(arr)
        True

        sage: arr = [45,32,12,1,1,6,32,45]; test_graphs(arr)
        True

        sage: arr = [117,80,24,1,1,12,80,117]; test_graphs(arr)
        True

        sage: arr = [3,2,2,2,1,1,1,3]; test_graphs(arr)
        True

        sage: arr = [4,3,3,3,1,1,1,4]; test_graphs(arr)
        True

        sage: arr = [5,4,4,4,1,1,1,5]; test_graphs(arr)
        True

        sage: arr = [6,5,5,4,1,1,2,6]; test_graphs(arr)
        True

        sage: arr = [6,5,5,5,1,1,1,6]; test_graphs(arr)
        True

        sage: arr = [8,7,6,5,1,2,3,8]; test_graphs(arr)
        True

        sage: arr = [8,7,7,7,1,1,1,8]; test_graphs(arr)
        True

        sage: arr = [9,8,8,8,1,1,1,9]; test_graphs(arr)
        True

        sage: arr = [10,9,9,9,1,1,1,10]; test_graphs(arr)
        True

        sage: arr = [12,11,10,7,1,2,5,12]; test_graphs(arr)
        True

        sage: arr = [12,11,11,11,1,1,1,12]; test_graphs(arr)
        True

        sage: arr = [13,12,12,4,1,1,9,13]; test_graphs(arr)
        True

        sage: arr = [15,14,10,3,1,5,12,15]; test_graphs(arr)
        True

        sage: arr = [15,14,12,8,1,3,7,15]; test_graphs(arr)
        True

        sage: arr = [24,23,22,21,1,2,3,24]; test_graphs(arr)
        True

        sage: arr = [27,26,24,19,1,3,8,27]; test_graphs(arr)
        True

        sage: arr = [32,31,30,17,1,2,15,32]; test_graphs(arr)
        True

        sage: arr = [40,39,36,27,1,4,13,40]; test_graphs(arr)
        True
    """

    G = distance_regular_graph(arr,check=False)
    arr2 = intersection_array_from_graph(G)
    return arr == arr2

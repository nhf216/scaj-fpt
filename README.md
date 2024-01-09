# scaj-fpt
Implementation of Fixed-Parameter Algorithm for Enumerating Most Parsimonious Scenarios in Single Cut-and-Join Rearrangement Model

The function count_MPS(c, m, w, n) in MPS_FPT.py is the implementation of the algorithm. Invoke this function by passing tuples of nonnegative integers for each of c, m, w, and n. Each integer in c should be at least 2, and each integer in m and w should be at least 1. These numbers represent the sizes of the crowns, M-shaped components, W-shaped compoments, and N-shaped components respectively. For example, count_MPS((2, 2), (3, 1), (3, 3, 2), (1, 1, 0)) determines the number of most parsimonious scenarios when the adjacency graph has two crowns (both of size 2), two M-shaped components (one with size 3 and one with size 1), three W-shaped components (two with size 3 and one with size 2), and three N-shaped components (two with size 1 and one with size 0).

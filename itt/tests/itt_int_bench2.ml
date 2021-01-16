extends Itt_int_test


thm test0 :
sequent { v1 : int; v2 : int; v3 : int; v4 : int; v5 : int; 
((8 *@ 'v3) +@ (4 *@ 'v2)) +@ ((3 *@ 'v4) +@ (6 *@ 'v2)) <> 5 *@ 'v2;
((8 *@ 'v4) +@ (1 *@ 'v4)) +@ ((7 *@ 'v4) +@ (6 *@ 'v1)) >= ((4 *@ 'v2) +@ (9 *@ 'v1)) +@ (0 *@ 'v5);
2 *@ 'v1 < 0 *@ 'v3;
(6 *@ 'v2) +@ ((3 *@ 'v5) +@ (0 *@ 'v2)) <= (8 *@ 'v1) +@ (2 *@ 'v4);
5 = ((7 *@ 'v3) +@ (2)) +@ ((6 *@ 'v2) +@ (2)) in int;
4 *@ 'v4 < ((4 *@ 'v1) +@ (5 *@ 'v5)) +@ (9);
4 *@ 'v1 < (1 *@ 'v4) +@ (1 *@ 'v1);
2 *@ 'v5 = 7 *@ 'v4 in int;
((7) +@ (0 *@ 'v4)) +@ ((5 *@ 'v1) +@ (7 *@ 'v2)) < 4 *@ 'v2;
((2 *@ 'v5) +@ (4 *@ 'v2)) +@ (6) <= 1;
(6 *@ 'v2) +@ (0) <> 1 *@ 'v1;
2 *@ 'v2 = ((0 *@ 'v3) +@ (2 *@ 'v4)) +@ ((7) +@ (3 *@ 'v5)) in int;
4 *@ 'v4 <> 0 *@ 'v3;
(4 *@ 'v4) +@ (1 *@ 'v2) <= 5 *@ 'v2;
(5 *@ 'v3) +@ ((5 *@ 'v5) +@ (8 *@ 'v1)) > (5 *@ 'v5) +@ ((2 *@ 'v4) +@ (8 *@ 'v5)) >- "false" } = "testT"

thm test1 :
sequent { v1 : int; v2 : int; v3 : int; v4 : int; v5 : int; 
((8) +@ (4 *@ 'v2)) +@ ((2 *@ 'v3) +@ (8 *@ 'v5)) >= (4 *@ 'v1) +@ (0 *@ 'v3);
9 <= ((1 *@ 'v5) +@ (1 *@ 'v3)) +@ (6 *@ 'v3);
4 *@ 'v2 >= 8 *@ 'v4;
(7 *@ 'v2) +@ ((9 *@ 'v2) +@ (6 *@ 'v1)) = 5 *@ 'v4 in int;
(4 *@ 'v4) +@ (6 *@ 'v5) >= ((8 *@ 'v3) +@ (4 *@ 'v2)) +@ ((9 *@ 'v4) +@ (0));
2 *@ 'v4 < 3 *@ 'v5;
(3 *@ 'v3) +@ (8) <> 8 *@ 'v1;
3 *@ 'v5 < (2 *@ 'v2) +@ (8 *@ 'v4);
(1 *@ 'v5) +@ ((8 *@ 'v5) +@ (2 *@ 'v1)) > ((8 *@ 'v3) +@ (2)) +@ ((1) +@ (1 *@ 'v5));
(5 *@ 'v3) +@ ((0 *@ 'v3) +@ (5 *@ 'v3)) <> ((4 *@ 'v3) +@ (0 *@ 'v4)) +@ ((0 *@ 'v2) +@ (3 *@ 'v5));
0 *@ 'v2 = ((5 *@ 'v4) +@ (1 *@ 'v5)) +@ (4 *@ 'v5) in int;
7 *@ 'v1 < 2 *@ 'v4;
((7 *@ 'v4) +@ (4 *@ 'v4)) +@ (0 *@ 'v4) = (4 *@ 'v1) +@ (2 *@ 'v3) in int;
5 *@ 'v2 = ((0 *@ 'v3) +@ (2)) +@ ((2 *@ 'v2) +@ (0 *@ 'v1)) in int;
8 *@ 'v3 = (9) +@ (9) in int >- "false" } = "testT"

thm test2 :
sequent { v1 : int; v2 : int; v3 : int; v4 : int; v5 : int; 
8 *@ 'v1 >= 6 *@ 'v2;
0 *@ 'v1 < (3) +@ ((3 *@ 'v4) +@ (1 *@ 'v3));
(8) +@ ((1 *@ 'v1) +@ (8 *@ 'v5)) > (5 *@ 'v2) +@ ((6 *@ 'v5) +@ (6 *@ 'v4));
((9 *@ 'v4) +@ (8 *@ 'v5)) +@ ((9 *@ 'v2) +@ (1)) <= ((9 *@ 'v3) +@ (7 *@ 'v4)) +@ (7 *@ 'v1);
3 *@ 'v1 <= (1 *@ 'v3) +@ ((9 *@ 'v2) +@ (0 *@ 'v1));
(0 *@ 'v5) +@ (3 *@ 'v3) = ((4) +@ (3)) +@ (4 *@ 'v4) in int;
1 *@ 'v2 > (8 *@ 'v4) +@ (6);
8 *@ 'v5 = 4 in int;
((5 *@ 'v1) +@ (5 *@ 'v4)) +@ ((9 *@ 'v2) +@ (8 *@ 'v4)) > ((2) +@ (7)) +@ ((0 *@ 'v2) +@ (7 *@ 'v2));
5 *@ 'v5 > 4;
((5 *@ 'v3) +@ (9 *@ 'v2)) +@ ((3 *@ 'v2) +@ (7)) = ((1) +@ (4)) +@ ((1 *@ 'v4) +@ (4 *@ 'v4)) in int;
(0 *@ 'v2) +@ (1) = (2 *@ 'v2) +@ (7 *@ 'v3) in int;
(8 *@ 'v1) +@ ((3 *@ 'v4) +@ (5 *@ 'v4)) <> (3 *@ 'v4) +@ ((6) +@ (1 *@ 'v3));
((4 *@ 'v2) +@ (8 *@ 'v4)) +@ ((7 *@ 'v1) +@ (6 *@ 'v5)) <= ((3 *@ 'v3) +@ (5 *@ 'v4)) +@ ((6 *@ 'v5) +@ (0 *@ 'v4));
5 *@ 'v5 > 7 *@ 'v4 >- "false" } = "testT"

thm test3 :
sequent { v1 : int; v2 : int; v3 : int; v4 : int; v5 : int; 
7 *@ 'v5 <= (5) +@ (2 *@ 'v3);
0 *@ 'v3 >= 8 *@ 'v5;
3 *@ 'v5 <= ((8 *@ 'v5) +@ (5 *@ 'v5)) +@ (4 *@ 'v5);
3 *@ 'v1 = 7 in int;
((1 *@ 'v4) +@ (5 *@ 'v3)) +@ (5) <= 6;
3 *@ 'v2 < 2 *@ 'v2;
7 < 9 *@ 'v5;
7 *@ 'v2 > (4) +@ (4 *@ 'v1);
7 *@ 'v4 < (1 *@ 'v3) +@ (9 *@ 'v2);
2 *@ 'v2 <> 4 *@ 'v5;
((6 *@ 'v5) +@ (5 *@ 'v5)) +@ (3 *@ 'v1) = 2 *@ 'v5 in int;
3 *@ 'v3 > 3 *@ 'v3;
7 *@ 'v3 <> 4 *@ 'v1;
(0) +@ (6 *@ 'v5) < 9 *@ 'v1;
((3 *@ 'v4) +@ (2 *@ 'v1)) +@ (2 *@ 'v1) > ((4 *@ 'v5) +@ (0)) +@ ((2) +@ (4 *@ 'v3)) >- "false" } = "testT"

thm test4 :
sequent { v1 : int; v2 : int; v3 : int; v4 : int; v5 : int; 
((0) +@ (7 *@ 'v1)) +@ ((5 *@ 'v2) +@ (7 *@ 'v2)) > 4 *@ 'v4;
6 *@ 'v4 <= ((2 *@ 'v5) +@ (5 *@ 'v2)) +@ ((3 *@ 'v5) +@ (3));
3 *@ 'v2 <= (4 *@ 'v5) +@ (7);
(5 *@ 'v2) +@ (0 *@ 'v4) >= ((3 *@ 'v2) +@ (9 *@ 'v5)) +@ ((5 *@ 'v1) +@ (1));
((7) +@ (2 *@ 'v2)) +@ ((7 *@ 'v1) +@ (3 *@ 'v2)) <= 8 *@ 'v3;
(8 *@ 'v3) +@ (1 *@ 'v4) >= (4 *@ 'v4) +@ (2 *@ 'v5);
(7 *@ 'v3) +@ (2 *@ 'v2) <= 9 *@ 'v3;
((4) +@ (8 *@ 'v4)) +@ (0 *@ 'v2) = 4 *@ 'v5 in int;
((6 *@ 'v4) +@ (8 *@ 'v1)) +@ ((1 *@ 'v5) +@ (5 *@ 'v1)) > 6 *@ 'v1;
((9 *@ 'v2) +@ (8 *@ 'v2)) +@ ((6 *@ 'v2) +@ (6 *@ 'v2)) <= ((6) +@ (3 *@ 'v3)) +@ ((1 *@ 'v4) +@ (7 *@ 'v5));
(4 *@ 'v1) +@ ((4 *@ 'v1) +@ (0 *@ 'v3)) < 6;
((7 *@ 'v3) +@ (0 *@ 'v5)) +@ ((6 *@ 'v2) +@ (7 *@ 'v3)) > (3 *@ 'v3) +@ (9 *@ 'v4);
(6) +@ ((0 *@ 'v3) +@ (0 *@ 'v4)) > ((9 *@ 'v1) +@ (3 *@ 'v4)) +@ (5 *@ 'v1);
(0 *@ 'v3) +@ (6 *@ 'v5) <= ((4) +@ (7 *@ 'v4)) +@ ((3 *@ 'v4) +@ (5));
(2 *@ 'v3) +@ ((2 *@ 'v5) +@ (6 *@ 'v5)) > (8 *@ 'v4) +@ (0) >- "false" } = "testT"

thm test5 :
sequent { v1 : int; v2 : int; v3 : int; v4 : int; v5 : int; 
((7 *@ 'v4) +@ (7 *@ 'v2)) +@ ((5 *@ 'v3) +@ (0 *@ 'v1)) <> ((4 *@ 'v3) +@ (3 *@ 'v2)) +@ ((7 *@ 'v2) +@ (1 *@ 'v5));
2 > (8 *@ 'v1) +@ (5 *@ 'v1);
1 *@ 'v5 <= ((3 *@ 'v4) +@ (4 *@ 'v1)) +@ ((0) +@ (0 *@ 'v5));
3 *@ 'v5 >= ((9 *@ 'v2) +@ (7 *@ 'v5)) +@ ((6 *@ 'v1) +@ (7 *@ 'v1));
5 *@ 'v4 <> 3 *@ 'v4;
((7 *@ 'v1) +@ (7)) +@ (4 *@ 'v3) > ((4 *@ 'v4) +@ (5)) +@ ((8 *@ 'v2) +@ (3 *@ 'v3));
(7 *@ 'v3) +@ ((6) +@ (5 *@ 'v1)) < 5 *@ 'v4;
1 *@ 'v4 < ((6 *@ 'v2) +@ (7 *@ 'v4)) +@ ((9 *@ 'v5) +@ (2 *@ 'v1));
6 *@ 'v3 >= (7) +@ (4 *@ 'v1);
((5 *@ 'v1) +@ (0 *@ 'v1)) +@ (1 *@ 'v1) < ((7 *@ 'v4) +@ (2 *@ 'v2)) +@ ((7 *@ 'v1) +@ (7));
6 *@ 'v4 < (6 *@ 'v1) +@ (6 *@ 'v3);
6 *@ 'v2 <> (1 *@ 'v1) +@ (9 *@ 'v4);
(8 *@ 'v2) +@ ((9) +@ (3)) = (5 *@ 'v2) +@ ((6 *@ 'v4) +@ (8 *@ 'v2)) in int;
((6 *@ 'v3) +@ (5 *@ 'v5)) +@ (0) <> 1 *@ 'v2;
1 *@ 'v5 <= 4 *@ 'v4 >- "false" } = "testT"

thm test6 :
sequent { v1 : int; v2 : int; v3 : int; v4 : int; v5 : int; 
2 *@ 'v1 = 0 *@ 'v1 in int;
((5 *@ 'v4) +@ (1 *@ 'v2)) +@ ((2 *@ 'v5) +@ (4 *@ 'v3)) <> ((1 *@ 'v3) +@ (9 *@ 'v5)) +@ (3 *@ 'v5);
0 *@ 'v5 <= 1 *@ 'v3;
(1) +@ ((8 *@ 'v3) +@ (8 *@ 'v2)) >= (7 *@ 'v5) +@ (5);
(1) +@ ((2) +@ (7)) <> (4 *@ 'v1) +@ ((2 *@ 'v5) +@ (3 *@ 'v1));
(7 *@ 'v3) +@ (0 *@ 'v1) >= (4 *@ 'v5) +@ (5 *@ 'v2);
3 *@ 'v5 <= (3 *@ 'v3) +@ (5 *@ 'v2);
(4 *@ 'v1) +@ (8 *@ 'v2) > 3 *@ 'v5;
(0 *@ 'v5) +@ ((7 *@ 'v2) +@ (0 *@ 'v3)) > (5 *@ 'v4) +@ ((7 *@ 'v4) +@ (4 *@ 'v4));
(6 *@ 'v3) +@ ((1 *@ 'v5) +@ (8 *@ 'v2)) >= (4 *@ 'v2) +@ ((5 *@ 'v4) +@ (1 *@ 'v3));
(5 *@ 'v1) +@ (9 *@ 'v1) > 5 *@ 'v3;
((4 *@ 'v2) +@ (0 *@ 'v1)) +@ (4 *@ 'v4) <= 3 *@ 'v5;
3 *@ 'v2 > 6 *@ 'v5;
3 *@ 'v3 > 5 *@ 'v2;
((8 *@ 'v3) +@ (9 *@ 'v5)) +@ (6 *@ 'v4) = 3 in int >- "false" } = "testT"

thm test7 :
sequent { v1 : int; v2 : int; v3 : int; v4 : int; v5 : int; 
(8 *@ 'v2) +@ ((7 *@ 'v4) +@ (8 *@ 'v4)) < (9 *@ 'v4) +@ ((0 *@ 'v4) +@ (8 *@ 'v4));
2 *@ 'v4 <> (2 *@ 'v3) +@ (7 *@ 'v1);
2 *@ 'v5 = 7 *@ 'v1 in int;
((7 *@ 'v4) +@ (1)) +@ (7 *@ 'v4) > (3 *@ 'v2) +@ (5);
(4 *@ 'v1) +@ ((0 *@ 'v4) +@ (7)) <> 9 *@ 'v2;
((0 *@ 'v4) +@ (7 *@ 'v4)) +@ ((2 *@ 'v4) +@ (1 *@ 'v3)) <= ((0) +@ (3 *@ 'v4)) +@ ((7 *@ 'v2) +@ (1 *@ 'v4));
((4) +@ (8 *@ 'v1)) +@ ((1 *@ 'v5) +@ (4 *@ 'v2)) = (8 *@ 'v3) +@ ((4 *@ 'v2) +@ (9 *@ 'v2)) in int;
((9 *@ 'v1) +@ (8 *@ 'v2)) +@ (2 *@ 'v4) > (4 *@ 'v4) +@ (0 *@ 'v2);
7 *@ 'v2 <> 0 *@ 'v4;
(4 *@ 'v5) +@ ((9) +@ (0 *@ 'v2)) < 9 *@ 'v2;
7 *@ 'v1 <= 3 *@ 'v5;
4 *@ 'v2 >= ((3 *@ 'v1) +@ (6 *@ 'v3)) +@ (4 *@ 'v5);
(2 *@ 'v3) +@ (2 *@ 'v2) <= ((1 *@ 'v1) +@ (1 *@ 'v2)) +@ (6 *@ 'v2);
(8 *@ 'v1) +@ ((1) +@ (0 *@ 'v2)) > 5 *@ 'v3;
8 *@ 'v3 = ((5 *@ 'v1) +@ (3 *@ 'v1)) +@ (4 *@ 'v4) in int >- "false" } = "testT"

thm test8 :
sequent { v1 : int; v2 : int; v3 : int; v4 : int; v5 : int; 
((6) +@ (3 *@ 'v4)) +@ ((0) +@ (6)) <> ((2 *@ 'v5) +@ (0 *@ 'v5)) +@ (1 *@ 'v3);
((3 *@ 'v1) +@ (4 *@ 'v1)) +@ ((7 *@ 'v2) +@ (4)) >= ((3 *@ 'v4) +@ (7 *@ 'v3)) +@ ((1 *@ 'v1) +@ (8 *@ 'v2));
6 *@ 'v1 < 6 *@ 'v1;
2 *@ 'v4 > (1 *@ 'v4) +@ (1 *@ 'v3);
(7 *@ 'v1) +@ ((0 *@ 'v1) +@ (2 *@ 'v1)) > (2 *@ 'v4) +@ ((4 *@ 'v2) +@ (7 *@ 'v3));
6 *@ 'v3 >= ((2) +@ (5)) +@ (6 *@ 'v4);
((7 *@ 'v4) +@ (1 *@ 'v3)) +@ ((6 *@ 'v5) +@ (4 *@ 'v2)) = 8 *@ 'v3 in int;
4 *@ 'v2 >= (3 *@ 'v3) +@ ((5 *@ 'v4) +@ (7 *@ 'v1));
6 *@ 'v4 < (6) +@ ((9 *@ 'v3) +@ (8 *@ 'v4));
(2 *@ 'v1) +@ (0 *@ 'v5) >= (6 *@ 'v3) +@ ((4 *@ 'v1) +@ (4 *@ 'v3));
0 *@ 'v4 >= 8 *@ 'v5;
0 *@ 'v1 <> 6 *@ 'v5;
((7 *@ 'v2) +@ (3 *@ 'v2)) +@ (2 *@ 'v3) <= (8 *@ 'v5) +@ (2 *@ 'v1);
(9 *@ 'v5) +@ ((5 *@ 'v2) +@ (7 *@ 'v4)) > ((0 *@ 'v1) +@ (1)) +@ (5 *@ 'v1);
(2 *@ 'v4) +@ ((7) +@ (1 *@ 'v1)) > 8 *@ 'v2 >- "false" } = "testT"

thm test9 :
sequent { v1 : int; v2 : int; v3 : int; v4 : int; v5 : int; 
(8 *@ 'v5) +@ (3 *@ 'v1) >= 5 *@ 'v5;
((9 *@ 'v4) +@ (0 *@ 'v1)) +@ ((9 *@ 'v3) +@ (9 *@ 'v4)) > ((8 *@ 'v3) +@ (5 *@ 'v1)) +@ (2 *@ 'v3);
((8 *@ 'v3) +@ (0 *@ 'v2)) +@ ((6 *@ 'v3) +@ (3 *@ 'v3)) < (3 *@ 'v4) +@ (2 *@ 'v4);
((8) +@ (4 *@ 'v5)) +@ (2) <= 4 *@ 'v2;
(8 *@ 'v3) +@ ((3 *@ 'v2) +@ (0 *@ 'v5)) <> (0 *@ 'v3) +@ (9 *@ 'v1);
(4 *@ 'v4) +@ (8 *@ 'v2) < (4 *@ 'v4) +@ (5 *@ 'v4);
5 *@ 'v4 <> ((9 *@ 'v1) +@ (0 *@ 'v2)) +@ (5 *@ 'v1);
0 *@ 'v3 > (3 *@ 'v3) +@ ((6 *@ 'v5) +@ (5 *@ 'v3));
2 *@ 'v3 <= ((9 *@ 'v3) +@ (5 *@ 'v5)) +@ (0 *@ 'v4);
6 *@ 'v3 >= 9 *@ 'v2;
((1 *@ 'v4) +@ (3 *@ 'v5)) +@ ((3 *@ 'v4) +@ (4 *@ 'v2)) <= 5 *@ 'v2;
(6) +@ ((9 *@ 'v2) +@ (3)) = 7 *@ 'v3 in int;
(1 *@ 'v5) +@ (1 *@ 'v1) = 8 *@ 'v5 in int;
((8 *@ 'v1) +@ (9 *@ 'v1)) +@ (5 *@ 'v5) < 3 *@ 'v2;
6 *@ 'v4 <> (3 *@ 'v4) +@ ((1 *@ 'v5) +@ (2 *@ 'v4)) >- "false" } = "testT"

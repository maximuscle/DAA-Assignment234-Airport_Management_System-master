#include "header.h"
#include <limits.h>
#include <stdio.h>
#include <string.h>

// This is just a sample test file.
// There will be hidden test cases for which you will be
// evaluated. Feel free to add test cases to this file.

// Fancy colors
#if defined(__linux__) || defined(__APPLE__)
#define PASSED "\033[1;32mPASSED\033[0m\n"
#define FAILED "\033[1;31mFAILED\033[0m\n"
#else
#define PASSED "\033[1;32mPASSED\033[0m\n"
#define FAILED "\033[1;31mFAILED\033[0m\n"
// #define PASSED "PASSED\n"
// #define FAILED "FAILED\n"
#endif

int t1_predicate_func(const airport_t *x, const airport_t *y)
{
    return strcmp(x->airport_name, y->airport_name) < 0;
}

int t2_predicate_func(const airport_t *x, const airport_t *y)
{
    return strcmp(x->airport_name, y->airport_name) > 0;
}

int t3_predicate_func(const airport_t *x, const airport_t *y)
{
    return (x->num_id % 10) < (y->num_id % 10);
}

int check_sorted(int n, const airport_t arr[n],
                 int (*predicate)(const airport_t *, const airport_t *))
{
    for (int i = 0; i < n - 1; ++i)
    {
        if (predicate(&arr[i+1], &arr[i]))
            return 0;
    }
    return 1;
}

int unordered_pair_compare(const pair_t *p1, const pair_t *p2)
{
	return ((p1->first == p2->first) && (p1->second == p2->second)) ||
		    ((p1->first == p2->second) && (p1->second == p2->first));
}

int check_edge_perm(const pair_t p[3], const pair_t *p1, const pair_t *p2, const pair_t *p3)
{
	return unordered_pair_compare(&p[0],p1) && unordered_pair_compare(&p[1],p2) && unordered_pair_compare(&p[2],p3);
}

int main()
{
    {
        // Q1
        {
            int n = 3;
            connection_t q1_t1_connections[3][3] = {
                {{0, 0}, {1, 2}, {2, 3}},
                 {{1, 2}, {0, 0}, {2, 3}},
                 {{2, 3}, {2, 3}, {0, 0}}};

            if (q1(n, q1_t1_connections))
            {
                printf("Q1 TestCase 1: " PASSED);
            }
            else
            {
                printf("Q1 TestCase 1: " FAILED);
            }
        }
        {
            int n = 3;
            connection_t q1_t2_connections[3][3] = {
                {{0, 0}, {INT_MAX, INT_MAX}, {3, 3}},
                {{INT_MAX, INT_MAX}, {0, 0}, {2, 3}},
                {{INT_MAX, INT_MAX}, {2, 3}, {0, 0}}};

            if (!q1(n, q1_t2_connections))
            {
                printf("Q1 TestCase 2: " PASSED);
            }
            else
            {
                printf("Q1 TestCase 2: " FAILED);
            }
        }
    }
    {
        // Q2
        {
            airport_t src = {0, "BLR"};
            airport_t dest = {1, "MUM"};
            int n = 3;
            int k = 2;
            connection_t q2_t1_connections[3][3] = {
                {{0, 0}, {INT_MAX, INT_MAX}, {1, 5}},
                {{1, 2}, {0, 0}, {4, 3}},
                {{2, 3}, {2, 3}, {0, 0}}};
            if (q2(&src, &dest, n, k, q2_t1_connections))
            {
                printf("Q2 TestCase 1: " PASSED);
            }
            else
            {
                printf("Q2 TestCase 1: " FAILED);
            }
        }
        {
            airport_t src = {0, "BLR"};
            airport_t dest = {1, "MUM"};
            int n = 4;
            int k = 2;
            connection_t q2_t2_connections[4][4] = {
                {{0, 0}, {INT_MAX, INT_MAX}, {1, 5}, {INT_MAX, INT_MAX}},
                {{1, 2}, {0, 0}, {4, 3}, {1, 4}},
                {{INT_MAX, INT_MAX}, {INT_MAX, INT_MAX}, {0, 0}, {2, 3}},
                {{1, 3}, {2, 4}, {INT_MAX, INT_MAX}, {0, 0}}};
            if (!q2(&src, &dest, n, k, q2_t2_connections))
            {
                printf("Q2 TestCase 2: " PASSED);
            }
            else
            {
                printf("Q2 TestCase 2: " FAILED);
            }
        }
        {
            {
            airport_t src = {0, "BLR"};
            airport_t dest = {3, "MUM"};
            int n = 4;
            int k = 2;
            connection_t q2_t3_connections[4][4] = {
                {{0, 0}, {INT_MAX, INT_MAX}, {1, 5}, {INT_MAX, INT_MAX}},
                {{1, 2}, {0, 0}, {4, 3}, {1, 4}},
                {{INT_MAX, INT_MAX}, {2, 3}, {0, 0}, {2, 3}},
                {{1, 3}, {2, 4}, {INT_MAX, INT_MAX}, {0, 0}}};
            if (q2(&src, &dest, n, k, q2_t3_connections))
            {
                printf("Q2 TestCase 3: " PASSED);
            }
            else
            {
                printf("Q2 TestCase 3: " FAILED);
            }
        }
        }
    }
    {
        // Q3
        {
            airport_t src = {0, "BLR"};
            int n = 3;
            connection_t q3_t1_connections[3][3] = {
                {{0, 0}, {1, 2}, {2, 3}},
                {{1, 2}, {0, 0}, {2, 3}},
                {{2, 3}, {2, 3}, {0, 0}}};

            if (q3(&src, n, q3_t1_connections))
            {
                printf("Q3 TestCase 1: " PASSED);
            }
            else
            {
                printf("Q3 TestCase 1: " FAILED);
            }
        }
        {
            airport_t src = {0, "BLR"};
            int n = 3;
            connection_t q3_t2_connections[3][3] = {
                {{0, 0}, {1, 2}, {2, 3}},
                {{INT_MAX, INT_MAX}, {0, 0}, {INT_MAX, INT_MAX}},
                {{2, 3}, {INT_MAX, INT_MAX}, {0, 0}}};

            if (q3(&src, n, q3_t2_connections))
            {
                printf("Q3 TestCase 2: " PASSED);
            }
            else
            {
                printf("Q3 TestCase 2: " FAILED);
            }
        }
        {
            airport_t src = {0, "BLR"};
            int n = 4;
            connection_t q3_t3_connections[4][4] = {
                {{0, 0}, {INT_MAX, INT_MAX}, {1, 5}, {INT_MAX, INT_MAX}},
                {{INT_MAX, INT_MAX}, {0, 0}, {4, 3}, {1, 4}},
                {{INT_MAX, INT_MAX}, {2, 3}, {0, 0}, {2, 3}},
                {{INT_MAX, INT_MAX}, {2, 4}, {INT_MAX, INT_MAX}, {0, 0}}};
            if (!q3(&src, n, q3_t3_connections))
            {
                printf("Q3 TestCase 3: " PASSED);
            }
            else
            {
                printf("Q3 TestCase 3: " FAILED);
            }
        }
    }
    {
        // Q4
        {
            int n = 5;
            airport_t q4_t1_airport_list[5] = {
                {0, "BLR"}, {1, "SUR"}, {2, "DEL"}, {3, "NEL"}, {4, "MUM"}};

            q4(n, t1_predicate_func, q4_t1_airport_list);
            if (check_sorted(n, q4_t1_airport_list, t1_predicate_func))
            {
                printf("Q4 TestCase 1: " PASSED);
            }
            else
            {
                printf("Q4 TestCase 1: " FAILED);
            }
        }
        {
            int n = 5;
            airport_t q4_t2_airport_list[5] = {
                {0, "BLR"}, {1, "SUR"}, {2, "DEL"}, {3, "NEL"}, {4, "MUM"}};

            q4(n, t2_predicate_func, q4_t2_airport_list);

            if (check_sorted(n, q4_t2_airport_list, t2_predicate_func))
            {
                printf("Q4 TestCase 2: " PASSED);
            }
            else
            {
                printf("Q4 TestCase 2: " FAILED);
            }
        }
        {
            int n = 5;
            airport_t q4_t3_airport_list[5] = {
                {0, "BLR"}, {10, "NEL"}, {11, "SUR"}, {22, "DEL"}, {4, "MUM"}};

            q4(n, t3_predicate_func, q4_t3_airport_list);

            if (check_sorted(n, q4_t3_airport_list, t3_predicate_func))
            {
                printf("Q4 TestCase 3: " PASSED);
            }
            else
            {
                printf("Q4 TestCase 3: " FAILED);
            }
        }
    }
    {
        // Q5
        {
            airport_t q5_t1_airports[] = {{0, "KOC"}, {1, "KIA"}, {2, "KOL"}};

            pair_t q5_t1_result = q5(3, q5_t1_airports);

            if ((q5_t1_result.first == 0 && q5_t1_result.second == 2) ||
                (q5_t1_result.first == 2 && q5_t1_result.second == 0))
            {
                printf("Q5 TestCase 1: " PASSED);
            }
            else
            {
                printf("Q5 TestCase 1: " FAILED);
            }
        }
        {
            airport_t q5_t2_airports[] = {{0, "BLR"}, {1, "MUM"}, {2, "KOL"}};
            pair_t q5_t2_result = q5(3, q5_t2_airports);

            if (q5_t2_result.first == -1 && q5_t2_result.second == -1)
            {
                printf("Q5 TestCase 2: " PASSED);
            }
            else
            {
                printf("Q5 TestCase 2: " FAILED);
            }
        }
    }
    {
        // Q6
        int q6_t1_entry_fee[] = {1, 2, 5, 10, 20, 25};
        int n = 6;

        int amount = 10;
        if (q6(n, amount, q6_t1_entry_fee) == 4)
        {
            printf("Q6 TestCase 1: " PASSED);
        }
        else
        {
            printf("Q6 TestCase 1: " FAILED);
        }

        amount = 30;
        if (q6(n, amount, q6_t1_entry_fee) == 6)
        {
            printf("Q6 TestCase 2: " PASSED);
        }
        else
        {
            printf("Q6 TestCase 2: " FAILED);
        }
    }
    {
         // Q7
        {
            int n = 3;
            const char *pat = "KO";
            int contains[3] = {0, 0, 0};
            airport_t q7_t1_airports[] = {{0, "KOCHI"}, {1, "KIA"}, {2, "KOLKATA"}};

            q7(n, pat, contains, q7_t1_airports);

            if (contains[0] == 1 && contains[1] == 0 && contains[2] == 1)
            {
                printf("Q7 TestCase 1: " PASSED);
            }
            else
            {
                printf("Q7 TestCase 1: " FAILED);
            }
        }
        {
            int n = 3;
            const char *pat = "U";
            int contains[3] = {0, 0, 0};
            airport_t q7_t2_airports[] = {{0, "BLR"}, {1, "MUM"}, {2, "KOL"}};

            q7(n, pat, contains, q7_t2_airports);

            if (contains[0] == 0 && contains[1] == 1 && contains[2] == 0)
            {
                printf("Q7 TestCase 2: " PASSED);
            }
            else
            {
                printf("Q7 TestCase 2: " FAILED);
            }
        }
        {
            int n = 3;
            const char *pat = "PleAse";
            int contains[3] = {0, 0, 0};
            airport_t q7_t3_airports[] = {{0, "PleAseant"}, {1, "asljAjdfPleAsee"}, {2, "JDF"}};

            q7(n, pat, contains, q7_t3_airports);

            if (contains[0] == 1 && contains[1] == 1 && contains[2] == 0)
            {
                printf("Q7 TestCase 3: " PASSED);
            }
            else
            {
                printf("Q7 TestCase 3: " FAILED);
            }
        }
    }
    {
        // Q8
        {
            connection_t q8_t1_connections[4][4] = {
                {{0, 0}, {7, 2}, {3, 5}, {INT_MAX, INT_MAX}},
                {{INT_MAX, INT_MAX}, {0, 0}, {INT_MAX, INT_MAX}, {1, 3}},
                {{INT_MAX, INT_MAX}, {2, 4}, {0, 0}, {4, 7}},
                {{4, 5}, {INT_MAX, INT_MAX}, {6, 3}, {0, 0}}};

            int n = 4;
            int trip_order[3] = {-1, -1, -1};

            int result = q8(n, trip_order, q8_t1_connections);

            if (result == 9 &&
                ((trip_order[0] == 1 && trip_order[1] == 3 && trip_order[2] == 2) ||
                (trip_order[0] == 2 && trip_order[1] == 1 && trip_order[2] == 3) ||
                (trip_order[0] == 3 && trip_order[1] == 2 && trip_order[2] == 1)))
            {
                printf("Q8 TestCase 1: " PASSED);
            }
            else
            {
                printf("Q8 TestCase 1: " FAILED);
            }
        }
        {
            connection_t q8_t2_connections[3][3] = {
                {{0, 0}, {1, 2}, {INT_MAX, INT_MAX}},
                {{INT_MAX, INT_MAX}, {0, 0}, {2, 3}},
                {{3, 4}, {INT_MAX, INT_MAX}, {0, 0}}};

            int n = 3;
            int trip_order[2] = {-1, -1};

            int result = q8(n, trip_order, q8_t2_connections);

            if (result == -1 && trip_order[0] == -1 && trip_order[1] == -1)
            {
                printf("Q8 TestCase 2: " PASSED);
            }
            else
            {
                printf("Q8 TestCase 2: " FAILED);
            }
        }
    }
    {
        // Q9
        {
            connection_t q9_t1_connections[4][4] = {
                {{0, 0}, {1, 2}, {2, 6}, {INT_MAX, INT_MAX}},
                {{1, 2}, {0, 0}, {3, 5}, {4, 1}},
                {{2, 6}, {3, 5}, {0, 0}, {5, 7}},
                {{INT_MAX, INT_MAX}, {4, 1}, {5, 7}, {0, 0}}};

            int n = 4;

            pair_t edges[3] = {{-1, -1}, {-1, -1}, {-1, -1}};
            int result = q9(n, edges, q9_t1_connections);
            pair_t p1 = {0, 1};
            pair_t p2 = {1, 2};
            pair_t p3 = {1, 3};
            if (result == 8 && (check_edge_perm(edges,&p1,&p2,&p3) || check_edge_perm(edges,&p1,&p3,&p2) ||
                check_edge_perm(edges,&p2,&p1,&p3) || check_edge_perm(edges,&p2,&p3,&p1) || check_edge_perm(edges,&p3,&p1,&p2) ||
                check_edge_perm(edges,&p3,&p2,&p1)))
            {
                printf("Q9 TestCase 1: " PASSED);
            }
            else
            {
                printf("Q9 TestCase 1: " FAILED);
            }
        }
        {
            connection_t q9_t2_connections[4][4] = {
            {{0, 0}, {1, 5}, {2, 3}, {2, 2}},
            {{1, 5}, {0, 0}, {3, 3}, {4, 7}},
            {{2, 3}, {3, 3}, {0, 0}, {5, 8}},
            {{2, 2}, {4, 7}, {5, 8}, {0, 0}}};

        int n = 4;

        pair_t edges[3] = {{-1, -1}, {-1, -1}, {-1, -1}};
        int result = q9(n, edges, q9_t2_connections);
		pair_t p1 = {0, 2};
		pair_t p2 = {0, 3};
		pair_t p3 = {1, 2};
        if (result == 8 && (check_edge_perm(edges,&p1,&p2,&p3) || check_edge_perm(edges,&p1,&p3,&p2) ||
            check_edge_perm(edges,&p2,&p1,&p3) || check_edge_perm(edges,&p2,&p3,&p1) || check_edge_perm(edges,&p3,&p1,&p2) ||
            check_edge_perm(edges,&p3,&p2,&p1)))
        {
            printf("Q9 TestCase 2: " PASSED);
        }
        else
        {
            printf("Q9 TestCase 2: " FAILED);
        }
        }
    }
    {
        // Q10
        {
            connection_t q10_t1_connections[4][4] = {
                {{0, 0}, {1, 2}, {2, 6}, {INT_MAX, INT_MAX}},
                {{1, 2}, {0, 0}, {3, 5}, {4, 1}},
                {{2, 6}, {3, 5}, {0, 0}, {5, 7}},
                {{INT_MAX, INT_MAX}, {4, 1}, {5, 7}, {0, 0}}};

            int n = 4;
            int k = 2;
            int destinations[] = {0, 2};
            int costs[2] = {INT_MAX, INT_MAX};

            airport_t src = {3, "BLR"};
            q10(n, k, &src, q10_t1_connections, destinations, costs);

            if (costs[0] == 3 && costs[1] == 6)
            {
                printf("Q10 TestCase 1: " PASSED);
            }
            else
            {
                printf("Q10 TestCase 1: " FAILED);
            }
        }
        {
            connection_t q10_t2_connections[4][4] = {
                {{0, 0}, {1, 2}, {2, 6}, {INT_MAX, INT_MAX}},
                {{1, 2}, {0, 0}, {3, 5}, {4, 1}},
                {{2, 6}, {3, 5}, {0, 0}, {5, 7}},
                {{INT_MAX, INT_MAX}, {4, 1}, {5, 7}, {0, 0}}};

            int n = 4;
            int k = 3;
            int destinations[] = {1, 2, 3};
            int costs[3] = {INT_MAX, INT_MAX, INT_MAX};

            airport_t src = {0, "BLR"};
            q10(n, k, &src, q10_t2_connections, destinations, costs);

            if (costs[0] == 2 && costs[1] == 6 && costs[2] == 3)
            {
                printf("Q10 TestCase 2: " PASSED);
            }
            else
            {
                printf("Q10 TestCase 2: " FAILED);
            }
        }
        {
            connection_t q10_t3_connections[4][4] = {
                {{0, 0}, {1, 5}, {2, 3}, {2, 2}},
                {{1, 5}, {0, 0}, {3, 3}, {4, 7}},
                {{2, 3}, {3, 3}, {0, 0}, {5, 8}},
                {{2, 2}, {4, 7}, {5, 8}, {0, 0}}};

            int n = 4;
            int k = 2;
            int destinations[] = {0, 1};
            int costs[2] = {INT_MAX, INT_MAX};

            airport_t src = {3, "BLR"};
            q10(n, k, &src, q10_t3_connections, destinations, costs);

            if (costs[0] == 2 && costs[1] == 7)
            {
                printf("Q10 TestCase 3: " PASSED);
            }
            else
            {
                printf("Q10 TestCase 3: " FAILED);
            }
        }
    }
    return 0;
}

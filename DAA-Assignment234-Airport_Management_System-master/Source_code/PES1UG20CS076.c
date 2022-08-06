#include "header.h"
#include <stdlib.h>
#include <limits.h>

// ANY STATIC FUNCTIONS ARE UP HERE

// dfs q1 helper function
static void q1_helper(int v, int n, int *visited, const connection_t (*conn)[n])
{
    visited[v] = 1;
    for (int i = 0; i < n; i++)
    {
        if (v != i && conn[v][i].distance != INT_MAX && visited[i] == 0)
            q1_helper(i, n, visited, conn);
    }
}

static int q2_helper(const int src, const int dest, int n,
                     int count, const connection_t (*conn)[n], int *visited)
{
    visited[src] = 1;
    if (src == dest)
    {
        if (count >= 0)
            return 1;
        // When you have reached the destination but took more flights than required
        return 0;
    }

    for (int v = 0; v < n; v++)
    {
        if(src != v && conn[src][v].distance != INT_MAX && visited[v] == 0 && count >= 0)
        {
            count--;
            int res = q2_helper(v, dest, n, count, conn, visited);
            if (res)
                return res;
            
            /*
                Need to unmark this as the path failed
                now it needs to check the next edge
            */
            visited[v] = 0;
            count++;
        }
    }

    // When you can't reach the destination
    return 0;
}

static void q3_helper(const int src, const int dest, const int n, const connection_t (*conn)[n], int *visited, int count, int *res)
{
    visited[src] = 1;
    if (src == dest && count != 0)
    {
        *res = 1;
        return;
    }
    if (count == 0)
        visited[dest] = 0;
    
    count++;
    
    for (int v = 0; v < n; v++)
    {
        if (src != v && conn[src][v].distance != INT_MAX && visited[v] == 0)
        {
            q3_helper(v, dest, n, conn, visited, count, res);
        }
    }
}

static void swap(airport_t *x, airport_t *y)
{
    airport_t temp = *x;
    *x = *y;
    *y = temp;
}

static int q4_partition(int n, int low, int high, int (*predicate_func)(const airport_t *, const airport_t *),
                        airport_t airport_list[n])
{
    int pivot = low;
    int left_pointer = low;
    int right_pointer = high + 1;

    do
    {
        do
        {
            left_pointer++;
        } while (left_pointer < high && predicate_func(&airport_list[left_pointer], &airport_list[pivot]));

        do
        {
            right_pointer--;
        } while (right_pointer > low && predicate_func(&airport_list[pivot], &airport_list[right_pointer]));

        if (left_pointer < right_pointer)
            swap(&airport_list[left_pointer], &airport_list[right_pointer]);
    } while (left_pointer < right_pointer);

    swap(&airport_list[pivot], &airport_list[right_pointer]);
    return right_pointer;
}

static void q4_helper_quicksort(int n, int low, int high, int (*predicate_func)(const airport_t *, const airport_t *),
                                airport_t airport_list[n])
{
    int p;
    if (low < high)
    {
        p = q4_partition(n, low, high, predicate_func, airport_list);
        q4_helper_quicksort(n, low, p - 1, predicate_func, airport_list);
        q4_helper_quicksort(n, p + 1, high, predicate_func, airport_list);
    }
}

static int str_len(const char *string)
{
    int len = 0;
    while(string[len] != '\0') len++;
    return len;
}

static int max(int a, int b)
{
    return (a >= b) ? a : b;
}

static int min(int a, int b)
{
    return (a < b) ? a : b;
}

static int longest_prefix_match(const char *string_1, const char *string_2, int length)
{
    int index = 0;
    while (index <= length - 1 && string_1[index] == string_2[index]) index++;
    return index;
}

static int string_compare(const char *string_1, const char *string_2, int len_1, int len_2)
{
    // Compares between the 2 strings and returns which is greater
    int length = max(len_1, len_2);
    int i = 0;
    int res = 0;
    char s1, s2;
    while(i < length && string_1[i] && string_2[i])
    {
        s1 = string_1[i];
        s2 = string_2[i++];
        
        if(s1 != s2)
        {
            res = s1 - s2;
            if(res > 0)
                return 1;
            return -1;
        }
    }
    return 0;
}

static void q5_string_sort(int n, airport_t airports[n], int start, int end)
{
    // Similar to the in-place quick sort for q4, this performs a quicksort for the given set of cities
    int pivot, i, j;
    airport_t temp;
    if(start < end)
    {
        i = start;
        j = end;
        pivot = start;
        while(i < j)
        {
            while(string_compare(airports[i].airport_name, airports[pivot].airport_name, str_len(airports[i].airport_name), 
                str_len(airports[pivot].airport_name)) == -1  && i < end)
                i++;
            
            while(string_compare(airports[j].airport_name, airports[pivot].airport_name, str_len(airports[j].airport_name), 
                str_len(airports[pivot].airport_name)) == 1  && j > start)                
                j--;
            if(i < j)
            {
                temp = airports[i];
                airports[i] = airports[j];
                airports[j] = temp;
            }
        }
        temp = airports[pivot];
        airports[pivot] = airports[j];
        airports[j] = temp; 
        q5_string_sort(n, airports, start, j - 1);
        q5_string_sort(n, airports, j + 1, end);
    }
}

static void create_shift_table(int *shift_table, const char *pat, int len, int table_length)
{
    for (int i = 0; i < table_length; i++)
        shift_table[i] = len;
    
    for (int i = 0; i < len - 1; i++)
        shift_table[(int) pat[i]] = len - i - 1;    
}

static int q7_helper_horspool(const char *pat, const char *text,
                              int m, int n, int *shift_table)
{
    /*
        Performing the regular horspool string matching with the help of a shift table
        which tell how much to shift on a bad match
    */
    int i = m - 1;
    int k;
    while (i < n)
    {
        k = 0;
        while (k < m && pat[m - 1 - k] == text[i - k])
            k++;
        
        if (k == m)
            return 1;
        
        i += shift_table[(int) text[i]];
    }

    return 0;
}

static int q8_count_in_list(int n, int selected[n])
{
    int count = 0;
    for(int i = 0; i < n; i++)
    {
        if(selected[i] == 1)
            count++;
    }
    return count;
}

static void q8_helper_1(int n, int trip_order[n - 1], int temp[n - 1], const connection_t connections[n][n],
                        int selected[n], int src, int temp_src, int index, int *min, int *cost)
{
    int i;
    int value;
    selected[src] = 1;

    for(i = 0; i < n; i++)
    {
        if(q8_count_in_list(n, selected) == n - 1)
        {
            int extra = connections[src][temp_src].distance;
            if(extra != INT_MAX)
            {
                temp[index] = src;
                *cost += extra;
                
                if(*cost <= *min)
                {
                    *min = *cost;
                    for(int j = 0; j < n - 1; j++)
                        trip_order[j] = temp[j];
                }
            }
            else
                extra = 0;

            *cost -= extra;
            i = n;
        }
        else if(connections[src][i].distance != 0 && connections[src][i].distance != INT_MAX && selected[i] == 0) 
        {
            value = connections[src][i].distance;
            temp[index++] = src;    
            *cost += value;     
            q8_helper_1(n, trip_order, temp, connections, selected, i, temp_src, index, min, cost);
            *cost -= value;
            index--;
        }
    }
    selected[src] = 0;
}

static int q9_find_minimum_edge_vertex(int *priority, int *inMST, int n)
{
    int minimum = INT_MAX;
    int v;
    for (int i = 0; i < n; i++)
    {
        if (inMST[i] == 0 && priority[i] < minimum)
        {
            v = i;
            minimum = priority[i];
        }
    }

    return v;
}

static void q10_helper_update_value(const int src, int *value, int *visited,
                                    int n, const connection_t (*conn)[n], const int cost)
{
    int temp = 0;
    for (int i = 0; i < n; i++)
    {
        // Replace the value with the least of the sum or the initial value
        if (src != i && conn[src][i].time != INT_MAX && visited[i] == 0)
        {
            temp = conn[src][i].time;
            value[i] = ((value[i] - (cost + temp) > 0) ? (cost + temp) : value[i]);
        }
    }
}

static void q10_dijkstra_path(int n, const connection_t (*conn)[n], const int source,
                              int *value, int *visited)
{
    int cost = 0;
    int minimum;
    int flag = source;

    for (int i = 0; i < n - 1; i++)
    {
        minimum = INT_MAX;
        q10_helper_update_value(flag, value, visited, n, conn, cost);

        for (int i = 0; i < n; i++)
        {
            if (i != source && minimum > value[i] && visited[i] == 0)
            {
                minimum = value[i];
                flag = i;
            }
        }
        visited[flag] = 1;
        cost += minimum;
    }
}

// YOUR SOLUTIONS BELOW

int q1(int n, const connection_t connections[n][n])
{
    int *visited = (int *) malloc(n * sizeof(int));

    /*
        Iterating through each vertex to see if it can visit every other vertex
        Performing a DFS for each vertex will tell whether every other vertex
        can be reached or not.
    */
    for (int v = 0; v < n; v++)
    {
        // Initializing the visited array everytime
        for (int i = 0; i < n; i++)
            visited[i] = 0;
        
        q1_helper(v, n, visited, connections);
        // Checking if all the vertices have been visited
        for (int i = 0; i < n; i++)
        {
            if (visited[i] == 0)
            {
                free(visited);
                return 0;
            }
        }
    }

    free(visited);
    return 1;
}

int q2(const airport_t *src, const airport_t *dest, int n, int k,
       const connection_t connections[n][n])
{
    if (src->num_id == dest->num_id)
        return 0;

    // Check the destination from source directly
    if (connections[src->num_id][dest->num_id].distance != INT_MAX)
    {
        k--;
        if (k >= 0)
            return 1;
    }

    int *visited = (int *) calloc(n, sizeof(int));
    int res = 0;
    
    res = q2_helper(src->num_id, dest->num_id, n, k, connections, visited);
    free(visited);

    return res;
}

int q3(const airport_t *src, int n, const connection_t connections[n][n])
{
    /*
        A DFS (or BFS) has to performed from for each edge node
        from the src node and see if it can reach back, if it can
        terminate the DFS and return 1, otherwise return 0
    */

    int *visited = (int *) calloc(n, sizeof(int));
    int count = 0;
    int res = 0;

    q3_helper(src->num_id, src->num_id, n, connections, visited, count, &res);
    free(visited);

    return res;
}

void q4(int n, int (*predicate_func)(const airport_t *, const airport_t *),
        airport_t airport_list[n])
{
    q4_helper_quicksort(n, 0, n - 1, predicate_func, airport_list);
}

pair_t q5(int n, airport_t airports[n])
{
    /*
        By performing a quick sort, we get a list with
        sorted cities, hence performing adjacent comparisions,
        which will provide the longest common prefix
    */
    pair_t ans = {-1, -1};
    int max = 0;
    int count;
    q5_string_sort(n, airports, 0, n - 1);
    for(int i = 0; i < n - 1; i++)
    {
        count = longest_prefix_match(airports[i].airport_name, airports[i + 1].airport_name, 
                min(str_len(airports[i].airport_name), str_len(airports[i + 1].airport_name)));
        
        if(count > max)
        {
            ans.first = airports[i].num_id;
            ans.second = airports[i + 1].num_id;
        }
    }
    return ans;
}

int q6(int n, int amount, const int entry_fee[n])
{
    /*
        We are given a sorted array with, hence we can use
        binary search to find whether the amount the traveller
        has is in the list or not
    */

    // if the amount is less than the least entry fee, they can't go to any airport
    if (amount < entry_fee[0])
        return 0;
    
    // if the amount is more than the costliest fee, then can go to any airport
    if (amount > entry_fee[n - 1])
        return n;
    
    int start = 0;
    int end = n - 1;
    int mid = (start + end) / 2;
    while (start <= end)
    {
        // The amount is in the middle of the search window
        if (entry_fee[mid] == amount)
            return mid + 1;
        if (entry_fee[mid] < amount)
            start = mid + 1;
        else
            end = mid - 1;
        mid = (end + start) / 2;
    }
    
    // The amount is in the middle of one of the entry fee pairs
    if (entry_fee[mid] < amount)
        return mid + 1;
    return mid - 1;
}

void q7(int n, const char *pat, int contains[n], const airport_t airports[n])
{
    int pat_len = str_len(pat);
    int airport_len = 0;
    int *shift_table = (int *) malloc(256 * sizeof(int));

    // Generating the shift table for Horspool's string matching
    create_shift_table(shift_table, pat, pat_len, 256);

    for (int i = 0; i < n; i++)
    {
        airport_len = str_len(airports[i].airport_name);
        contains[i] = q7_helper_horspool(pat, airports[i].airport_name, pat_len, airport_len, shift_table);
    }

    free(shift_table);
}

int q8(int n, int trip_order[n - 1], const connection_t connections[n][n])
{
    int in_list[n];
    int lowest = INT_MAX;
    int min = INT_MAX;
    int i, j;
    int index = 0, cost = 0;
    int temp[n - 1];

    for (i = 0; i < n; i++)
    {
        for (j = 0; j < n; j++)
            in_list[j] = 0;

        q8_helper_1(n, trip_order, temp, connections, in_list, i,
                    i, index, &min, &cost);

        if(min < lowest)
            lowest = min;
        cost = 0;
    }  
    if (min == INT_MAX)
    {
        lowest = -1;
        for(i = 0; i < n - 1; i++)
            trip_order[i] = -1;
    }
    return lowest;
}

int q9(int n, pair_t edges[n - 1], const connection_t connections[n][n])
{
    /*
        To find the path which follows the constraints, we need to find
        the minimum spanning tree, which can be done using prim's or kurskal's
        algorithm, Implementation done using prim's algorithm
    */

    // To keep track of vertices in MST
    int *inMST = (int *) calloc(n, sizeof(int));
    int *parent = (int *) malloc(n * sizeof(int));
    int *priority = (int *) malloc(n * sizeof(int));
    int v;
    int cost = 0;

    // Initially none will have the priority
    for (int i = 0; i < n; i++)
        priority[i] = INT_MAX;
    
    // Assuming starting node is 0, hence it has no parent
    parent[0] = -1;
    priority[0] = 0;

    // n vertices will have n - 1 edges
    for (int i = 0; i < n - 1; i++)
    {
        v = q9_find_minimum_edge_vertex(priority, inMST, n);
        inMST[v] = 1;

        for (int j = 0; j < n; j++)
        {
            if(connections[v][j].time != INT_MAX && inMST[j] == 0 && connections[v][j].time < priority[j])
            {
                priority[j] = connections[v][j].time;
                parent[j] = v;
            }
        }
    }

    for (int i = 0; i < n - 1; i++)
    {
        edges[i].first = parent[i + 1];
        edges[i].second = i + 1;
        cost += connections[edges[i].first][edges[i].second].time;
    }

    free(inMST);
    free(parent);
    free(priority);
    return cost;
}

void q10(int n, int k, const airport_t *src,
         const connection_t connections[n][n], const int destinations[k],
         int costs[k])
{
    /*
        Dijkstra's algorithm will be able to return the shortest path
        from the source to the destination, which is implemented here
    */

    int *value = (int *) malloc(n * sizeof(int));
    int *visited = (int *) malloc(n * sizeof(int));

    // Initially all the values will be infinity from the starting edge
    for (int i = 0; i < n; i++)
    {
        value[i] = INT_MAX;
        visited[i] = 0;
    }
    
    // Taking the value of source in the array to be 0, as the cost starts from here
    value[src->num_id] = 0;
    visited[src->num_id] = 1;

    q10_dijkstra_path(n, connections, src->num_id, value, visited);

    for (int i = 0; i < k; i++)
        costs[i] = value[destinations[i]];
    
    free(value);
    free(visited);
}

// END

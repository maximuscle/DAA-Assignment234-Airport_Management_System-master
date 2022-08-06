#ifndef HEADER_H_
#define HEADER_H_

/*
**
** Please go through the document shared with you thoroughly and carefully.
** DO NOT MODIFY THIS FILE.
**
*/

/*
 * Structure representing an airport.
 * Every airport contains a unique ID and name.
 */
struct airport
{
    int num_id;
    const char *airport_name;
};
typedef struct airport airport_t;

/*
 * The connection represents the details of an edge in the connection graph.
 * graph[i][j] will be a connection structure containg the time and distance
 * from airport with id=i to airport with id=j.
 */
struct connection
{
    int distance;
    int time;
};
typedef struct connection connection_t;

/*
 * This structure is used as a return value and parameters in some functions.
 */
struct pair
{
    int first;
    int second;
};
typedef struct pair pair_t;

/*
 * @param n: Total number of airports
 * @param connections: Adjacency matrix which is a graph representing the
 * connections between the airports
 *
 * @return value: 1 if it is possible for a traveler to be able to go from any
 * airport to any other airport, directly or indirectly, and this being true for
 * all airports, else 0
 */
int q1(int n, const connection_t connections[n][n]);

/*
 * @param src: The source airport
 * @param dest: The destination airport
 * @param n: Total number of airports
 * @param k: The maximum number of flights
 * @param connections: Adjacency matrix which is a
   graph representing the connections between the airports
 *
 * @return value: boolean variable indicating if it is possible to reach dest
 from src using at most k flights
 */
int q2(const airport_t *src, const airport_t *dest, int n, int k,
       const connection_t connections[n][n]);

/*
 * @param src: Start and end airport
 * @param n: Total number of airports
 * @param connections: Adjacency matrix which is a
   graph representing the connections between the airports
 *
 * @return value: boolean variable indicating if it is possible to start at the
 src airport and return to the src airport
 *
 */
int q3(const airport_t *src, int n, const connection_t connections[n][n]);

/*
 * @param airport_list: list of all airports
 * @param n: Total number of airports
 * @param predicate_func: Function pointer to the comparator function
 *
 * The array must be sorted *in-place* according to the predicate after the
 * function call
 */
void q4(int n, int (*predicate_func)(const airport_t *, const airport_t *),
        airport_t airport_list[n]);

/*
 * @param n: The number of airports in the array airports
 * @param airports: An array of type airport containing the details of various
 * airports
 *
 * @return value: A pair containing the num_ids of the 2 airports that have the
 * longest common prefix names, return {-1,-1} if no names have a common prefix.
 * The IDs may be in any order within the pair.
 */
pair_t q5(int n, airport_t airports[n]);

/*
 * @param n: Total number of airports
 * @param amount: Amount of money you have
 * @param entry_fee: *Sorted* array containing entry fee of all airports
 *
 * @return_value: Number of airports you may be able to visit given the amount
 * of money available to you
 */
int q6(int n, int amount, const int entry_fee[n]);

/*
 * @param n: Total number of airports
 * @param pat: Pattern to search in the list of airport names
 * @param contains: array of size n initialized to 0
 * @param airports: list of all airports
 *
 * At the end of the function, contains[i] should be 1 if the airport with
 * num_id i contains pat as a substring in its name
 */
void q7(int n, const char *pat, int contains[n], const airport_t airports[n]);

/*
 * @param n: Total number of airports
 * @param trip_order: An array of size n-1 which contains the trip order
 initialized to -1s.
 * @param connections: Adjacency matrix which is a graph representing the
 connections between the airports
 *
 * @return value: The minimum cost of the round trip. If no such trip exists,
 return -1.
 *
 * At the end of the function, trip order must contain the trip in the minimum
 sequence.
 */
int q8(int n, int trip_order[n - 1], const connection_t connections[n][n]);

/*
 * @param n: Total number of airports
 * @param edges: Array of type pair_t of length n-1 initialized to {-1,-1}.
 * @param connections: Adjacency matrix which is an undirected
   graph representing the connections between the airports
 *
 * @return value: Minimum total time
 *
 * At the end of the function must be filled with the edges belonging to the
 solution. The edges are represented by a pair with the start node and end node
 of the edge. The edges may be in any order. The start and end order in the pair
 is not important as it is undirected. All equivalent solutions are accepted.
 */
int q9(int n, pair_t edges[n - 1], const connection_t connections[n][n]);

/*
 * @param n: Total number of airports
 * @param k: Number of destination airports
 * @param src: The source of travel to the destinations
 * @param connections: Adjacency matrix which is a
   graph representing the connections between the airports
 * @param destinations: Array of airport IDs that you will need to find the
 minimum time for.
 * @param costs: An integer array of length k that will be initialized to
 INT_MAX
 *
 * At the end of the function, costs must be filled with the minimum cost for
 the corresponding destination airport. costs[i] must be the minimum time taken
 to travel to destination[i].
 */
void q10(int n, int k, const airport_t *src,
         const connection_t connections[n][n], const int destinations[k],
         int costs[k]);

#endif // HEADER_H_

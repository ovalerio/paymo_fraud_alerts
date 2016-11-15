/*
 * fraud-alert.cpp
 *
 * This program is intended to alert users about suspicious payments
 * It uses and underlying graph, where users are at the graph nodes
 * and the connecting edges are given by the existing historic payments
 * between users.
 *
 *  Created on: 09.11.2016
 *      Author: ovalerio
 */
#include <fstream>
#include <iostream>
#include <exception>
#include <iomanip>
#include <sstream>
#include <string>
#include <utility>
#include <vector>
#include <set>
#include <map>
#include <climits>

#include <boost/config.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/adjacency_list.hpp>
#include <boost/property_map/property_map.hpp>
#include <boost/graph/breadth_first_search.hpp>

using namespace std;
using namespace boost;

// payment struct is modeled after PayMo payment records
// a record consists of five fields separated by commas:
// time, id1, id2, amount, message
// 2016-11-02 09:49:29, 52575, 1120, 25.32, Spam
typedef struct {
	std::string time; // the timestamp is being stored as a string.
	int id1; // warning: casting to integer without input validation
	int id2; // warning: casting to integer without input validation
	std::string amount; // since we are not using amount we keep it as a string
	std::string message;
} payment_t;

typedef vector<payment_t> data_t;

// Graph Definitions
typedef adjacency_list<vecS, vecS, undirectedS> Graph;
typedef graph_traits<Graph>::vertex_descriptor Vertex;
typedef graph_traits<Graph>::vertices_size_type Size;
typedef graph_traits<Graph>::edge_descriptor Edge;

typedef int UID;
typedef Vertex Node;

typedef std::map<UID, Node> UserMap; //key->UID; value-> Node
typedef std::map<Node, UID> NodeMap; //key->Node; value-> UID
typedef std::pair<Node, Node> Connection;

// users and nodes have a one-to-one association
UserMap users;
NodeMap nodes;

// mantain a set of all one-to-one friendships (using map)
map<long, bool> friends;

// attempting to minimize the time it takes to test if a connection exists
// using the perfect hash function posted by nawfal in stackoverflow
// REF: http://stackoverflow.com/questions/919612/mapping-two-integers-to-one-in-a-unique-and-deterministic-way
static long perfect_hash(int a, int b){
	unsigned long A = (unsigned long)(a >= 0 ? 2 * (long)a : -2 * (long)a - 1);
	unsigned long B = (unsigned long)(b >= 0 ? 2 * (long)b : -2 * (long)b - 1);
	long C = (long)((A >= B ? A * A + A + B : A + B * B) / 2);
	return (a < 0 && b < 0 )|| (a >= 0 && b >= 0) ? C : -C - 1;
}

// By convention we create connections always using the smaller node number
// in the first position and the bigger node number in the second position
Connection create_connection(Node node1, Node node2) {
	Connection connection;
	if (node1 < node2) {
		connection.first = node1;
		connection.second = node2;
	} else {
		connection.first = node2;
		connection.second = node1;
	}
	return connection;
}

// this function maps a userid with a corresponding payment graph node
// this function also register the association between a node and userid.
Node add_user(UID uid, Graph& g) {
	Node node;
	UserMap::iterator it = users.find(uid);
	if (it != users.end()) {
		node = it->second;
	} else {
		node = add_vertex(g);
		users.insert(std::make_pair(uid, node));
		nodes.insert(std::make_pair(node, uid));
	}
	return node;
}

// this method updates the payment graph creating an edge between the nodes in case there is none
void update_network(Connection connection, Graph& g) {
	Vertex v0 = connection.first;
	Vertex v1 = connection.second;
	// the payment network is updated only if there is no prior transactions between users
	if (!edge(v0, v1, g).second) { // according to our convention v0 is always smaller than v1
		add_edge(v0, v1, g); // adding new edge to paymo graph
		friends[perfect_hash(v0, v1)] = true;
	}
}

// this method process all payments, registering PayMo users and existing payment connections
void build_paymo_network(data_t& payment_data, Graph& g) {
	for (unsigned int indx = 0; indx < payment_data.size(); indx++) {
		payment_t payment = payment_data[indx];
		UID uid1 = payment.id1;
		UID uid2 = payment.id2;
		Node node1 = add_user(uid1, g);
		Node node2 = add_user(uid2, g);
		Connection connection = create_connection(node1, node2);
		update_network(connection, g);
	}
}

// overloading input stream operator to read a single PayMo batch_payment record
istream& operator >>(istream& is, payment_t& record) {

	// the entire payment record is first read into a string and then parsed out
	// NOTE: each payment record occupies a line and values are separated by comma
	string line;
	getline(is, line);

	// separating the comma delimited values out of the line
	stringstream ss(line);
	string id1_field, id2_field;
	getline(ss, record.time, ',');
	getline(ss, id1_field, ',');
	getline(ss, id2_field, ',');
	getline(ss, record.amount, ',');
	getline(ss, record.message);

	stringstream id1fss(id1_field);
	stringstream id2fss(id2_field);
	id1fss >> record.id1;
	id2fss >> record.id2;

	return is;
}

// overloading the input stream operator to read a list of PayMo payment records
istream& operator >>(istream& is, data_t& data) {
	// since we reuse our payment database, both for the batch_payment and stream_payment
	// we clear the database every time we read a new payment file.
	data.clear();

	// removing the first line of the payment CSV file (PayMo header)
	string header_line;
	getline(is, header_line);

	// Reading records from file and appending them to the payment database
	payment_t record;
	while (is >> record) {
		data.push_back(record);
	}

	return is;
}

// Visualization of paymo network using graphviz (*.dot file)
// NOTE: the build directory must have a directory called figs
void build_visualization(Graph g) {
	std::ofstream fout("figs/paymo-network.dot");
	fout << "digraph A {\n" << "  rankdir=LR\n" << "size=\"5,3\"\n"
			<< "ratio=\"fill\"\n" << "edge[style=\"bold\"]\n"
			<< "node[shape=\"oval\"]\n";

	graph_traits<Graph>::edge_iterator ei, ei_end;
	for (tie(ei, ei_end) = edges(g); ei != ei_end; ++ei)
		fout << nodes[source(*ei, g)] << " -> " << nodes[target(*ei, g)]
				<< "[label=1]\n";

	fout << "}\n";
}

/* NOTE: to optimize performance a customized visitor is used
 * halting execution when the target node is found. The halting
 * visitor code was adapted from stackoverflow. The bfs distance
 * visitor was modelled after the Bacon Number example from Boost.
 * REF1: http://stackoverflow.com/questions/32047840/make-boost-dijkstra-algorithm-stop-when-it-reaches-a-destination-node
 * REF2: http://www.boost.org/doc/libs/1_54_0/libs/graph/example/kevin-bacon.cpp
 */

// Throwing an exception is the preferred mechanism used to stop search in boost
#define stop_search_exception 404

// Visitor that throw an exception whenever it finds the target node
template < typename DistanceMap >
class bfs_distance_visitor :public default_bfs_visitor{
private:
	DistanceMap d;
	Vertex stop_vertex;
public:
	bfs_distance_visitor(DistanceMap d, Vertex stop_vertex) :
		d(d), stop_vertex(stop_vertex) {};

    template <typename Edge, typename Graph>
    void tree_edge(Edge e, const Graph& g) const
    {
      Vertex u = source(e, g);
      Vertex v = target(e, g);
      d[v] = d[u] + 1;
      if (v == stop_vertex)
    	  throw (stop_search_exception);
    }
};

// record_bfs_distance is a convenience wrapper used to access the bfs_distance_visitor
template < typename DistanceMap >
bfs_distance_visitor<DistanceMap>
record_bfs_distance(DistanceMap d, Vertex stop_vertex){
	return bfs_distance_visitor< DistanceMap > (d, stop_vertex);
}

/* The friendship_degree method runs a breadth_first_search algorithm to determine
 * the distance between the start node (conn.first) and the target node (conn.second).
 */
int friendship_degree(Connection connection, Graph& g) {

	// Initializing breadth first search parameters
	Node start_node = connection.first;
	Node stop_node = connection.second;
	Vertex start_vertex = vertex(start_node, g);
	Vertex stop_vertex = vertex(stop_node, g);
	std::vector<int> d(num_vertices(g), (std::numeric_limits<int>::max)());
	d[start_node] = 0; // setting the start_node distance from itself

	try {
		breadth_first_search(g, start_vertex, visitor(record_bfs_distance(&d[0], stop_vertex)));
	} catch (int exception) { /* Ignored */ }

	return d[stop_node];
}


int main() {

	// A database will be used to hold our payment records
	data_t payment_data;

	// STEP 1: Reading batch payment data from CSV file
	ifstream batch_file("paymo_input/batch_payment.csv");
	batch_file >> payment_data;

	if (!batch_file.eof()) {
		cout << "Error while reading the *batch* payment file. Aborting.\n";
		return 1;
	}

	cout << "The *batch* payment file contains " << payment_data.size() << " records.\n";
	batch_file.close();

	// STEP 2: Constructing a graph with the payment information contained in the batch CSV file
	Graph g;
	build_paymo_network(payment_data, g);

	// STEP 3: Reading stream payment data from CSV file
	ifstream stream_file("paymo_input/stream_payment.csv");
	stream_file >> payment_data;

	if (!stream_file.eof()) {
		cout << "Error while reading the *stream* payment file. Aborting.\n";
		return 1;
	}

	cout << "The *stream* payment file contains " << payment_data.size() << " records.\n";
	batch_file.close();

	// STEP 4: Main processing loop. Stream payments are read sequentially and output files written
	ofstream output1("paymo_output/output1.txt");
	ofstream output2("paymo_output/output2.txt");
	ofstream output3("paymo_output/output3.txt");

	for (unsigned int indx = 0; indx < payment_data.size(); indx++) {

		payment_t payment = payment_data[indx];
		UID uid1 = payment.id1;
		UID uid2 = payment.id2;
		Node node1 = add_user(uid1, g);
		Node node2 = add_user(uid2, g);
		Connection connection = create_connection(node1, node2);

		int friendship;

		if (friends[perfect_hash(connection.first, connection.second)]) {
			// if a direct connection exists between both nodes (users) then no alert is needed
			friendship = 1;
			std::cout << "Existing friendship between USER:" << uid1 << " and USER:" << uid2 << std::endl;
		} else {
			// for all other cases we will use boost::dijkstra_search_algorithm
			friendship = friendship_degree(connection, g);
			update_network(connection, g); // updating PayMo payment graph
			std::cout << "The friendship degree between USER:" << uid1 << " and USER:" << uid2 << " is " << friendship << std::endl;
		}

		output1 << (friendship>1? "Unverified" : "Trusted") << std::endl;
		output2 << (friendship>2? "Unverified" : "Trusted") << std::endl;
		output3 << (friendship>4? "Unverified" : "Trusted") << std::endl;

	}

	output1.close();
	output2.close();
	output3.close();

	/* Visualization of PayMo network */
	build_visualization(g);

	cout << "Processing completed.\n";
	return 0;
}


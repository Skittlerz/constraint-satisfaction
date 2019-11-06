// CS421-A3-ABraun.cpp : This file contains the 'main' function. Program execution begins and ends there.
// Amanda Braun

#include <iostream>
#include <math.h>
#include <vector>
#include <tuple>
#include <string>
#include <random>
#include <cmath>
#include <ctime>
#include <chrono>

//-----------CSP MODEL FUNCTIONS--------------------
void generateInstance(int n, double p, double a, double r);
bool inTupleList(std::tuple<int, int> tup);
bool inPairList(std::tuple<int, int> pair, const std::vector< std::tuple<int, int>> &pairs);
void setUndirectedArcs();
void printInstance();

//-----------ARC CONSISTENCY FUNCTIONS--------------------
void arcConsistency(std::vector<std::tuple<int, int>> arcs,
	std::vector<std::vector<std::tuple<int, int>>> arc_pairs);
bool revise(std::tuple<int, int> arc, std::vector<std::tuple<int, int>> arc_pair);

//-----------BACKTRACKING FUNCTIONS--------------------
void backtrackingSearch(const std::vector<int> &variables);
bool backtrack(int var_index, int domain_index);
bool isSafe(int var,
	int val,
	const std::vector<std::tuple<int, int>> &constraints,
	const std::vector< std::vector< std::tuple<int, int> >> &constraint_pairs);

//-----------BACKTRACKING WITH FORWARD CHECKING FUNCTIONS------------------
void forwardCheckingSearch(const std::vector<int> &variables);
bool backtrackWithForwardChecking(int var_index, int domain_index, std::vector<std::vector<int>> &temp_domain);
bool forwardCheck(int var, int val, std::vector<std::vector<int>> &temp_domain);
bool removeInconsistentArc(std::tuple<int, int> tuple, int val2, std::vector<std::vector<int>> &temp_domain);

//-----------BACKTRACKING WITH FULL LOOK AHEAD FUNCTIONS------------------
void fullLookAheadSearch(const std::vector<int> &variables);
bool backtrackWithFullLookAhead(int var_index, int domain_index, std::vector<std::vector<int>> &temp_domain);
bool fullLookAhead(int var, int val, std::vector<std::vector<int>> &temp_domain);

//-----------GENERAL HELPER FUNCTIONS--------------------
bool solutionSatisfied();
void printSolution();
template < typename T>
std::pair<bool, int > findInVector(const std::vector<T>  & vecOfElements, const T  & element);
void checkSolution();
bool isDomainEmpty(std::vector<std::vector<int>> &temp_domain);

// GLOBAL VARS

int domain_size; 
int constraints_count;
int incompatible_tuples_count;
const double EulerConstant = std::exp(1.0);
std::chrono::high_resolution_clock::time_point start, end;
// constraint containers
// index of incompatible tuple corresponds to index of incompatible pairs
std::vector<std::tuple<int, int>> incompatible_tuples, rev_incompatible_tuples, undirected_incompatible_tuples; //ex. <X1, X3>
std::vector< std::vector< std::tuple<int, int> >> incompatible_pairs, rev_incompatible_pairs, undirected_incompatible_pairs; // ex. [ (0,1), (1,2)]
//variable containter 
std::vector<int> variables; //ex. X0, X1, ...
//solution container
std::vector<int> solution;
//domain container - domain instance is kept for each variable
std::vector<std::vector<int>> domains;


int main()
{
	bool running = true;
	while (running) {
		int run_program;
		std::cout << "----CSP Solver----\n";
		std::cout << "Exit?\n";
		std::cout << "1. Yes\n";
		std::cout << "2. No\n";
		std::cout << ">";
		std::cin >> run_program;

		if (run_program == 1) {
			running = false;
			break;
		}

		int n;
		double p, a, r;
		//get parameter input from user:
		std::cout << "Enter number of variables:\n";
		std::cout << ">";
		std::cin >> n;

		std::cout << "Enter constraint tightness:\n";
		std::cout << ">";
		std::cin >> p;

		std::cout << "Enter constant a:\n";
		std::cout << ">";
		std::cin >> a;

		std::cout << "Enter constant r:\n";
		std::cout << ">";
		std::cin >> r;

		int algorithm_select;
		int arc_select;
		std::cout << "Select Search Algorithm: \n";
		std::cout << "1. Standard Backtracking\n";
		std::cout << "2. BT with Forward Checking\n";
		std::cout << "3. BT with Full Look Ahead\n";
		std::cout << ">";
		std::cin >> algorithm_select;
		std::cout << "Run Arc Consistency?\n";
		std::cout << "1. Yes\n";
		std::cout << "2. No\n";
		std::cout << ">";
		std::cin >> arc_select;

		// Phase transition pt is calculated as follows:
		// pt = 1 - e^ (-a / r)
		double pt = 1 - pow(EulerConstant, -a / r);
		// Solvable problems are therefore generated with p < pt
		if (p < pt) {

			generateInstance(n, p, a, r);
			setUndirectedArcs(); // Each arc constraint is undirected - account for both directions
			printInstance();

			if (arc_select == 1) {
				arcConsistency(undirected_incompatible_tuples, undirected_incompatible_pairs);
			}
			start = std::chrono::high_resolution_clock::now();
			switch (algorithm_select)
			{
			case 1:
				backtrackingSearch(variables);
				break;
			case 2:
				forwardCheckingSearch(variables);
				break;
			case 3:
				fullLookAheadSearch(variables);
				break;
			default:
				break;
			}
		}
		else {
			std::cout << "Parameters lead to unsolvable problem." << std::endl;
		}
	}

}

//-----------CSP MODEL FUNCTIONS--------------------

void generateInstance(int n , double p, double a, double r)
{	
	//domain size - n^a
	domain_size = round( pow(n, a) );
	//constraints - r n ln n
	constraints_count = round( r * n * (log(n)) );
	//incompatible tuples - pd^2
	incompatible_tuples_count = round( p * pow(domain_size, 2) );

	//set variables
	variables.clear();
	for (int var = 0; var < n; var++) {
		variables.push_back(var);
	}
	//set domain for each variable
	domains.clear();
	std::vector<int> dx;
	for (int d = 0; d < n; d++) {
		dx.clear();
		for (int el = 0; el < domain_size; el++) {
			dx.push_back(el);
		}
		domains.push_back(dx);
	}

	std::random_device rd; // obtain a random number from hardware
	std::mt19937 eng(rd()); // seed the generator
	std::uniform_int_distribution<> var_distr(0, n - 1); // range defined by number of variables
	int val1, val2;
	std::tuple<int, int> temp, rev_temp;

	//randomly generate a set of constraints
	incompatible_tuples.clear();
	rev_incompatible_tuples.clear();
	for (int c = 0; c < constraints_count; c++) {
		do {
			val1 = var_distr(eng);
			var_distr.reset(); // generate independent values

			do {
				val2 = var_distr(eng);
				var_distr.reset();
			} while (val1 == val2); //each constraint requires two unique variables

			temp = std::make_tuple(val1, val2);
			rev_temp = std::make_tuple(val2, val1);
		} while (inTupleList(temp)); //if random constraint selection already exists, try again...

		incompatible_tuples.push_back(temp);
		rev_incompatible_tuples.push_back(rev_temp);
	}

	std::uniform_int_distribution<> domain_distr(0, domain_size - 1); //range defined by domain size
	int pair1, pair2;
	std::tuple<int, int> pair_temp, rev_pair_temp;
	std::vector<std::tuple<int, int>> tuple_temp, rev_tuple_temp;

	//randomly generate a set of incompatible pairs for each constraint
	incompatible_pairs.clear();
	rev_incompatible_pairs.clear();
	for(int t = 0; t < incompatible_tuples.size(); t++){
		tuple_temp.clear();
		rev_tuple_temp.clear();
		for (int i = 0; i < incompatible_tuples_count; i++) {
			do {
				pair1 = domain_distr(eng);
				domain_distr.reset();
				pair2 = domain_distr(eng);
				domain_distr.reset();
				pair_temp = std::make_tuple(pair1, pair2);
				rev_pair_temp = std::make_tuple(pair2, pair1);
			} while (inPairList(pair_temp, tuple_temp)); //if random pair selection exists, try again...

			tuple_temp.push_back(pair_temp);
			rev_tuple_temp.push_back(rev_pair_temp);
		}

		incompatible_pairs.push_back(tuple_temp);
		rev_incompatible_pairs.push_back(rev_tuple_temp);
	}
}

bool inTupleList(std::tuple<int, int> tup) {
	bool found = false;
	std::tuple<int, int> reversed_tup = std::make_tuple(std::get<1>(tup), std::get<0>(tup));
	for (int t = 0; t < incompatible_tuples.size(); t++) {
		//for constraints (X1, X2) and (X2, X1) are considered equal
		//need to check for both cases
		if (tup == incompatible_tuples[t] || reversed_tup == incompatible_tuples[t]) {
			found = true;
		}
	}
	return found;
}

bool inPairList(std::tuple<int, int> pair, const std::vector< std::tuple<int, int>> &pairs) {
	bool found = false;
	for (int i = 0; i < pairs.size(); i++) {
		if (pair == pairs[i]) {
			found = true;
		}
	}
	return found;
}

void setUndirectedArcs() {

	undirected_incompatible_pairs.clear();
	undirected_incompatible_pairs.reserve(incompatible_pairs.size() + rev_incompatible_pairs.size());
	undirected_incompatible_pairs.insert(undirected_incompatible_pairs.end(), incompatible_pairs.begin(), incompatible_pairs.end());
	undirected_incompatible_pairs.insert(undirected_incompatible_pairs.end(), rev_incompatible_pairs.begin(), rev_incompatible_pairs.end());

	undirected_incompatible_tuples.clear();
	undirected_incompatible_tuples.reserve(incompatible_tuples.size() + rev_incompatible_tuples.size());
	undirected_incompatible_tuples.insert(undirected_incompatible_tuples.end(), incompatible_tuples.begin(), incompatible_tuples.end());
	undirected_incompatible_tuples.insert(undirected_incompatible_tuples.end(), rev_incompatible_tuples.begin(), rev_incompatible_tuples.end());
}

void printInstance() {
	std::cout << "-----CSP Binary Instance-----\n";
	std::cout << "Domain Size = " << domain_size << std::endl;
	std::cout << "Number of Constraints = " << constraints_count << std::endl;
	std::cout << "Number of Incomaptible Tuples = " << incompatible_tuples_count << std::endl;
	std::cout << "Variables: { ";
	for (auto & element : variables) {
		std::cout << "X" << element << " ";
	}
	std::cout << "}\n";
	std::cout << "Domain: { ";
	for (auto & element : domains[0]) {
		std::cout << element << " ";
	}
	std::cout << "}\n";
	std::cout << "Constraints: Incompatible Tuples\n";
	for (int t = 0; t < incompatible_tuples.size(); t++) {
		std::cout << "(X" << std::get<0>(incompatible_tuples[t]) << ", ";
		std::cout << "X" << std::get<1>(incompatible_tuples[t]) << "): ";
		for (int i = 0; i < incompatible_pairs[t].size(); i++) {
			std::cout << "(" << std::get<0>(incompatible_pairs[t][i]) << ","; 
			std::cout << std::get<1>(incompatible_pairs[t][i]) << ") ";
		}
		std::cout << std::endl;
	}
}

//-----------ARC CONSISTENCY FUNCTIONS--------------------

void arcConsistency(std::vector<std::tuple<int, int>> arcs, 
	std::vector<std::vector<std::tuple<int,int>>> arc_pairs) {
	
	std::tuple<int, int> arc;
	std::vector<std::tuple<int, int>> arc_pair;
	while (!arcs.empty()) { 

		arc = arcs.front(); //pop first arc from queue
		arcs.erase(arcs.begin());
		arc_pair = arc_pairs.front(); //pop corresponding incompatible arc pairs
		arc_pairs.erase(arc_pairs.begin());

		if (revise(arc, arc_pair)) { //if domain was reduced
			int x = std::get<0>(arc);
			int y = std::get<1>(arc);
			for (int i = 0; i < undirected_incompatible_tuples.size(); i++) {
				if (std::get<1>(undirected_incompatible_tuples[i]) == x
					&& std::get<0>(undirected_incompatible_tuples[i]) != y) { //add neighbours (k, x) to queue
					std::pair<bool, int> inList = findInVector(arcs, undirected_incompatible_tuples[i]);
					if(!inList.first){ // arcs = arcs U neighbours - check if already in arcs
						arcs.push_back(undirected_incompatible_tuples[i]);
						arc_pairs.push_back(undirected_incompatible_pairs[i]);
					}
				}
			}
		}
	}
}

// parameter arc(i,j) represents variable constraint pair
// parameter arc_pair is a list of incompatible values for arc(i, j)
bool revise(std::tuple<int, int> arc, std::vector<std::tuple<int, int>> arc_pair)
{
	
	bool removed = false;
	//variable form is X1, X2, ..
	//grab last char and convert to int
	int a = std::get<0>(arc); // i
	int b = std::get<1>(arc); // j

	std::vector < std::vector<std::tuple<int, int>>> grouped_pairs;
	std::vector <std::tuple<int, int>> group;

	//group arc pairs that share the same i value
	for (int ai = 0; ai < domains[a].size(); ai++) {
		group.clear();
		for (int pair = 0; pair < arc_pair.size(); pair++) {
			if (domains[a][ai] == std::get<0>(arc_pair[pair])) {
				group.push_back(arc_pair[pair]);
			}
		}

		if(!group.empty())
			grouped_pairs.push_back(group);
	}

	std::vector<int> temp_domain;
	for (int g1 = 0; g1 < grouped_pairs.size(); g1++) { //for each grouping
		temp_domain = domains[b];
		for (int g2 = 0; g2 < grouped_pairs[g1].size(); g2++) { //iterate over incompatible b values
			std::pair<bool, int> b_result = findInVector(temp_domain, std::get<1>(grouped_pairs[g1][g2]));
			if (b_result.first)
				temp_domain.erase(temp_domain.begin() + b_result.second); //remove incompatible b value from temp_domain
				
				
		}
		if (temp_domain.empty()) { //no suitable b value left 
			std::pair<bool, int> a_result = findInVector(domains[a], std::get<0>(grouped_pairs[g1][0]));
			if (a_result.first) {
				domains[a].erase(domains[a].begin() + (a_result.second)); //remove a from di domain
				removed = true;
			}
		}
	}

	return removed;
}

//-----------BACKTRACKING FUNCTIONS--------------------

void backtrackingSearch(const std::vector<int> &variables)
{
	//initialize solution 
	solution.resize(variables.size());
	for (int v = 0; v < variables.size(); v++) {
		solution[v] = -1;
	}

	if (!backtrack(0, 0)) {
		std::cout << "Solution does not exist.\n";
	}
	else {
		end = std::chrono::high_resolution_clock::now();
		printSolution();
	}
}

bool backtrack(int var_index, int domain_index)
{
	if (solutionSatisfied()) { // all variables have been satisfied
		return true;
	}
	int var = variables[var_index];

	for (int x = 0; x < domains[domain_index].size(); x++) { // for each element in the variable's domain

		if (isSafe(var, domains[domain_index][x], undirected_incompatible_tuples, undirected_incompatible_pairs)) { // ensure assignment doesn't violate constraints
			solution[var_index] = domains[domain_index][x];

			if (backtrack(var_index + 1, domain_index + 1)) { //recursively assign value to next variable
				return true;
			}

			domains[domain_index].erase(domains[domain_index].begin() + x); // no safe assignment for this domain element - remove from domain
		}
	}

	return false;
}

bool isSafe(int var, 
	int val, 
	const std::vector<std::tuple<int, int>> &constraints,
	const std::vector< std::vector< std::tuple<int, int> >> &constraint_pairs)
{
	for (int i = 0; i < constraints.size(); i++) {
		
		if (var == std::get<0>(constraints[i])) {
			int var2 = std::get<1>(constraints[i]); // get second var in constraint	

			for (int j = 0; j < constraint_pairs[i].size(); j++) { // check each constraint pair
				
				if (std::get<0>(constraint_pairs[i][j]) == val) { // if selected value is present in constraint pair
					int val2 = std::get<1>(constraint_pairs[i][j]); // get second value in constraint pair
					if (var2 < solution.size() && solution[var2] == val2) { // if second value is already assigned the second value in constraint pair
						return false;
					}
				}
			}
		}
	}

	return true;
}

//-----------BACKTRACKING WITH FORWARD CHECKING FUNCTIONS--------------------

void forwardCheckingSearch(const std::vector<int> &variables)
{
	//initialize solution 
	solution.resize(variables.size());
	for (int v = 0; v < variables.size(); v++) {
		solution[v] = -1;
	}
	std::vector< std::vector<int> > temp_domain = domains;
	if (!backtrackWithForwardChecking(0, 0, temp_domain)) {
		std::cout << "Solution does not exist.\n";
	}
	else {
		end = std::chrono::high_resolution_clock::now();
		printSolution();
	}
}

bool backtrackWithForwardChecking(int var_index, int domain_index, std::vector<std::vector<int>> &temp_domain)
{
	if (solutionSatisfied()) { // all variables have been satisfied
		return true;
	}
	int var = variables[var_index];

	for (int x = 0; x < temp_domain[domain_index].size(); x++) { // for each element in the variable's domain

		std::vector<std::vector<int>> prev_state_domain = temp_domain;
		if (forwardCheck(var, temp_domain[domain_index][x], temp_domain)) { // perform forward checking
			solution[var_index] = temp_domain[domain_index][x];

			if (backtrackWithForwardChecking(var_index + 1, domain_index + 1, temp_domain)) { //recursively assign value to next variable
				return true;
			}
			//else {
			//	for (int i = var_index + 1; i < temp_domain.size(); i++) {
			//		temp_domain[i] = prev_state_domain[i]; // if unsuccessful, need to reset changes made
			//	}
			//}
		}
		else {
			for (int i = var_index + 1; i < temp_domain.size(); i++) {
				temp_domain[i] = prev_state_domain[i]; // if unsuccessful, need to reset changes made
			}
		}
	}

	return false;
}

bool forwardCheck(int var, int val, std::vector<std::vector<int>> &temp_domain) {

	// create queue of constraints (k, i)
	std::vector<std::tuple<int, int>> queue;
	for (int t = 0; t < undirected_incompatible_tuples.size(); t++) {
		int k = std::get<0>(undirected_incompatible_tuples[t]);
		int i = std::get<1>(undirected_incompatible_tuples[t]);
		if (i == var && solution[k] == -1) {
			queue.push_back(undirected_incompatible_tuples[t]);
		}
	}

	bool not_consistent = false;

	while (!queue.empty() && !not_consistent) {
		std::tuple<int, int> q = queue.front();
		queue.erase(queue.begin());
		if (removeInconsistentArc(q, val, temp_domain)) {
			not_consistent = isDomainEmpty(temp_domain); 
		}
	}

	return !not_consistent;
}

bool removeInconsistentArc(std::tuple<int, int> tuple, int val2, std::vector<std::vector<int>> &temp_domain) {

	int var1 = std::get<0>(tuple);
	int var2 = std::get<1>(tuple);
	bool removed = false;
	std::pair<bool, int> tuple_index = findInVector(undirected_incompatible_tuples, tuple);
	if (tuple_index.first) {

		for (int i = 0; i < undirected_incompatible_pairs[tuple_index.second].size(); i++) {

			if (val2 == std::get<1>(undirected_incompatible_pairs[tuple_index.second][i])) {
				int val1 = std::get<0>(undirected_incompatible_pairs[tuple_index.second][i]);
				std::pair<bool, int> domain_index = findInVector(variables, var1);
				if (domain_index.first) {
					std::pair<bool, int> domain_value = findInVector(temp_domain[domain_index.second], val1);
					if (domain_value.first) {
						temp_domain[domain_index.second].erase(temp_domain[domain_index.second].begin() + domain_value.second); // remove inconsistent value from domain
						removed = true;
					}
				}
			}
		}
	}

	return removed;

}

//-----------BACKTRACKING WITH FULL LOOK AHEAD FUNCTIONS--------------------

void fullLookAheadSearch(const std::vector<int> &variables)
{
	//initialize solution 
	solution.resize(variables.size());
	for (int v = 0; v < variables.size(); v++) {
		solution[v] = -1;
	}
	std::vector< std::vector<int> > temp_domain = domains;
	if (!backtrackWithFullLookAhead(0, 0, temp_domain)) {
		std::cout << "Solution does not exist.\n";
	}
	else {
		end = std::chrono::high_resolution_clock::now();
		printSolution();
	}
}

bool backtrackWithFullLookAhead(int var_index, int domain_index, std::vector<std::vector<int>> &temp_domain)
{
	if (solutionSatisfied()) { // all variables have been satisfied
		return true;
	}
	int var = variables[var_index];

	for (int x = 0; x < temp_domain[domain_index].size(); x++) { // for each element in the variable's domain

		std::vector<std::vector<int>> prev_state_domain = temp_domain;
		if (fullLookAhead(var, temp_domain[domain_index][x], temp_domain)) { // perform full look ahead
			solution[var_index] = temp_domain[domain_index][x];

			if (backtrackWithFullLookAhead(var_index + 1, domain_index + 1, temp_domain)) { //recursively assign value to next variable
				return true;
			}
			else {
				for (int i = var_index + 1; i < temp_domain.size(); i++) {
					temp_domain[i] = prev_state_domain[i];
				}
			}
		}
		else {
			for (int i = var_index + 1; i < temp_domain.size(); i++) {
				temp_domain[i] = prev_state_domain[i];
			}
		}
	}

	return false;
}

bool fullLookAhead(int var, int val, std::vector<std::vector<int>> &temp_domain) {

	// create queue of constraints (k, i)
	std::vector<std::tuple<int, int>> queue;
	for (int t = 0; t < undirected_incompatible_tuples.size(); t++) {

		int k = std::get<0>(undirected_incompatible_tuples[t]);
		int i = std::get<1>(undirected_incompatible_tuples[t]);
		if (i == var && solution[k] == -1) {
			queue.push_back(undirected_incompatible_tuples[t]);
		}
	}

	bool not_consistent = false;

	while (!queue.empty() && !not_consistent) {

		std::tuple<int, int> q = queue.front();
		queue.erase(queue.begin());
		int x = std::get<1>(q);
		int y = std::get<0>(q);
		if (removeInconsistentArc(q, val, temp_domain)) {

			not_consistent = isDomainEmpty(temp_domain);
	
			for (int i = 0; i < undirected_incompatible_tuples.size(); i++) {

				if (std::get<1>(undirected_incompatible_tuples[i]) == x
					&& std::get<0>(undirected_incompatible_tuples[i]) != y) { //add neighbours (k, x) to queue - k =/= y
					std::pair<bool, int> inList = findInVector(queue, undirected_incompatible_tuples[i]);
					if (!inList.first) { // queue = queue U neighbours - check if already in queue
						queue.push_back(undirected_incompatible_tuples[i]);
					}
				}
			}
		}
	}

	return !not_consistent;
}

//-----------GENERAL HELPER METHODS--------------------

bool solutionSatisfied() {
	for (int i = 0; i < solution.size(); i++) {
		if (solution[i] == -1) {
			return false;
		}
	}
	return true;
}

void printSolution() {
	std::cout << "-----Solution----\n";

	for (int v = 0; v < variables.size(); v++) {
		std::cout << "X" << variables[v] << " = " << solution[v] << std::endl;
	}

	std::cout << "Time = ";
	std::cout << std::chrono::duration_cast<std::chrono::nanoseconds>(end - start).count() << " ns\n";

}

// Find given element in vector
template < typename T>
std::pair<bool, int > findInVector(const std::vector<T>  & vec_of_elements, const T  & element)
{
	std::pair<bool, int > result;

	auto it = std::find(vec_of_elements.begin(), vec_of_elements.end(), element);

	if (it != vec_of_elements.end())
	{
		result.second = distance(vec_of_elements.begin(), it);
		result.first = true;
	}
	else
	{
		result.first = false;
		result.second = -1;
	}

	return result;
}

void checkSolution() {
	bool correct = true;
	for (int i = 0; i < undirected_incompatible_tuples.size(); i++) {
		std::tuple<int, int> current = undirected_incompatible_tuples[i];
		int var1 = std::get<0>(current);
		int var2 = std::get<1>(current);
		int a1 = solution[var1];
		int a2 = solution[var2];
		for (int j = 0; j < undirected_incompatible_pairs[i].size(); j++) {
			int val1 = std::get<0>(undirected_incompatible_pairs[i][j]);
			int val2 = std::get<1>(undirected_incompatible_pairs[i][j]);

			if (val1 == a1 && val2 == a2) {
				correct = false;
				std::cout << var1 << " = " << a1 << std::endl;
				std::cout << var2 << " = " << a2 << std::endl;
				std::cout << "conflicts with constraint: " << val1 << " " << val2 << std::endl;
			}
		}
	}

	if (correct) {
		std::cout << "Solution verified\n";
	}
}

bool isDomainEmpty(std::vector<std::vector<int>> &domain)
{
	for (int d = 0; d < domain.size(); d++) {
		if (domain[d].empty())
			return true;
	}

	return false;
}



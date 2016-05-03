// Brian Goldman

#include <iostream>
using namespace std;
#include "Problem.h"
#include <fstream>
using std::ofstream;
// This is a heuristic I have for picking what to merge
bool second_better(const std::shared_ptr<DNF>& first, const std::shared_ptr<DNF>& second) {
  if (first->get_table().size() > 100 or second->get_table().size() > 100) {
    return first->get_table().size() > second->get_table().size();
  } else if (first->get_variables().size() < second->get_variables().size()) {
    return true;
  } else if (first->get_variables().size() > second->get_variables().size()) {
    return false;
  } else {
    return first->get_table().size() > second->get_table().size();
  }
}

void heuristic_merge(Problem& problem) {
  auto first = *problem.dnfs.begin();
  for (const auto new_first : problem.dnfs) {
    if (second_better(first, new_first)) {
      first = new_first;
    }
  }
  auto second = *problem.dnfs.begin();
  for (const auto new_second : problem.dnfs) {
    if (second == new_second) {
      second = new_second;
    } else if (new_second != first and second_better(second, new_second)) {
      second = new_second;
    }
  }
  std::weak_ptr<DNF> weak_first = first;
  std::weak_ptr<DNF> weak_second = second;
  problem.merge(weak_first, weak_second);
}

int main(int argc, char * argv[]) {
  if (argc < 2) {
    cout << "Must specify an input file" << endl;
    return 1;
  }
  Problem problem;
  problem.load(argv[1]);
  problem.print_short(std::cout);
  cout << "Problem load complete" << endl;
  problem.knowledge_propagate();
  problem.sanity_check();
  problem.print_short(std::cout);
  cout << "Finished normal propagate" << endl;
  problem.make_singles();
  problem.print_short();
  cout << "Make Singles complete" << endl;
  problem.break_down();
  problem.clear_identical();
  problem.print_short();
  cout << "Finished breakdown" << endl;
  unordered_map<size_t, size_t> frequencies;
  for (const auto bin : problem.variable_to_dnfs) {
    frequencies[bin.size()]++;
  }
  cout << "Frequency of variables: ";
  print_map(frequencies, cout);
  unordered_map<size_t, size_t> function_sizes;
  for (const auto dnf : problem.dnfs) {
    function_sizes[dnf->get_table().size()]++;
  }
  cout << "Frequency of number-of-rows: ";
  print_map(function_sizes, cout);
  problem.convert_to_dimacs("temp.dimacs");
  return 0;
}

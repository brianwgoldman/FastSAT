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
  problem.global_knowledge.print();
  problem.print_short(std::cout);
  cout << "Finished normal propagate" << endl;
  problem.print_short(std::cout);
  /*
  cout << "Two-to-one begin" << endl;
  problem.two_to_one();
  cout << "Two-to-one done" << endl;
  //*/

  while (problem.make_singles()) {
    problem.print_short();
    break;
  }
  cout << "Starting assume-and-learn" << endl;
//  problem.equal_variable_assuming();
  cout << "Ending assume and learn, brining out of cold storage" << endl;

  /*
  for (const auto dnf : problem.cold_storage) {
    problem.add_dnf(dnf);
  }
  problem.cold_storage.clear();
  //*/
  return 0;
  problem.break_down();
  problem.print_short();
  problem.clear_identical();
  problem.print_short();
  problem.knowledge_propagate();
  unordered_map<size_t, size_t> frequencies;
  for (const auto bin : problem.variable_to_dnfs) {
    frequencies[bin.size()]++;
  }
  print_map(frequencies, cout);

  std::ofstream out("temp.txt");
  unordered_map<size_t, size_t> function_sizes;
  problem.print(out);
  /*
  for (const auto dnf : problem.dnfs) {
    dnf->print_short(out);
  }
  */
  out << "Begin cold storage" << endl;
  for (const auto dnf : problem.cold_storage) {
    dnf->print(out);
  }
  out << "Begin problem knowledge" << endl;
  problem.global_knowledge.print(out);
  for (const auto dnf : problem.dnfs) {
    function_sizes[dnf->get_table().size()]++;
  }
  print_map(function_sizes, cout);
  problem.print_short(cout);
  problem.knowledge_propagate();
  problem.print_short(cout);
  return 0;
  for (size_t i=0; problem.dnfs.size() > 0 and i < 1000; i++) {
    heuristic_merge(problem);
    problem.knowledge_propagate();
    problem.assume_and_learn();
  }
  //problem.sanity_check();
  cout << "Finished merge+assume-and-learn" << endl;
  problem.global_knowledge.print();
  problem.print();
  return 0;
}

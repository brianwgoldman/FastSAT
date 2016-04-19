// Brian Goldman

#include <iostream>
using namespace std;
#include "Problem.h"

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
  /*problem.print();
  unordered_map<size_t, size_t> counts;
  for (const auto & dnf : problem.dnfs) {
    for (const auto v : dnf->get_variables()) {
      counts[v]++;
    }
  }
  //print_map(counts, cout);
  unordered_map<size_t, size_t> freq_counts;
  for (const auto pair : counts) {
    freq_counts[pair.second]++;
  }
  print_map(freq_counts, cout);
  std::weak_ptr<DNF> weak_best;
  size_t score = -1;
  for (const auto & dnf : problem.dnfs) {
    weak_dnf_set overlaps;
    for (const auto v : dnf->get_variables()) {
      overlaps.insert(problem.variable_to_dnfs[v].begin(), problem.variable_to_dnfs[v].end());
    }
    if (score > overlaps.size()) {
      score = overlaps.size();
      weak_best = dnf;
    }
  }
  weak_best.lock()->print();
  cout << "Overlaps: " << score << endl;
  auto realized = weak_best.lock();
  problem.assume_and_learn(realized);
  realized->create_knowledge().print();
  return 0;
  //*/
  problem.print_short(std::cout);
  problem.equal_variable_assuming();
  problem.print_short(std::cout);
  return 0;
  cout << "Starting assume-and-learn" << endl;
  problem.assume_and_learn();
  problem.sanity_check();
  cout << "Finished first assume-and-learn" << endl;
  //problem.print();
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

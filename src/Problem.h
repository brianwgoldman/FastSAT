// This class encodes the entire problem (DNFs and Knowledge)
// and knows how to manipulate the problem
#ifndef PROBLEM_H_
#define PROBLEM_H_
// TODO "propagate_assumption" can screw with "knowledge_propagate" by making
// the problem think DNFs have been propagated even when they haven't.
// TODO Remove smart pointers and replace with regular pointers
#include <memory>
#include <iostream>
#include <set>
#include <unordered_set>

#include "DNF.h"
#include "Knowledge.h"

using std::string;

// This is a "set" and not an "unordered_set" because weak_ptr doesn't
// have a safe, immutable hash function
using weak_dnf_set=std::set<std::weak_ptr<DNF>,std::owner_less<std::weak_ptr<DNF>>>;

class Problem {
 public:
  void load(const string& filename);
  void print(std::ostream& out=std::cout) const;
  void print_short(std::ostream& out=std::cout) const;

  void knowledge_propagate();
  void propagate_assumption(Knowledge& assumption);

  void assume_and_learn();
  std::weak_ptr<DNF> merge(std::weak_ptr<DNF>& weak_a, std::weak_ptr<DNF>& weak_b);

  // TODO most of these things should probably be private
  std::unordered_set<std::shared_ptr<DNF>> dnfs;
  vector<weak_dnf_set> variable_to_dnfs;
  weak_dnf_set requires_knowledge_propagate;
  weak_dnf_set requires_assume_and_learn;
  Knowledge global_knowledge;
  void sanity_check();
 private:
  std::weak_ptr<DNF> resolve_overlaps(std::weak_ptr<DNF>& weak_dnf);
  void knowledge_propagate(Knowledge& knowledge, bool modify_in_place);
  void load_dnf(const string& filename);
  void load_cnf(const string& filename);
  void add_knowledge(const Knowledge& knowledge);
  //Knowledge knowledge_propagate(const Knowledge& knowledge, weak_dnf_set& open_set, bool modify_in_place);
  void add_dnf(const std::shared_ptr<DNF>& dnf);
  void remove_dnf(std::weak_ptr<DNF>& weak_dnf);
  void clean_up_bins(const unordered_set<size_t>& require_updating);

  //std::shared_ptr<DNF> simple_convert(vector<std::unordered_map<size_t, bool>>& rows);
  std::shared_ptr<DNF> old_convert(vector<std::unordered_map<size_t, bool>>& rows);
  std::shared_ptr<DNF> smart_convert(vector<std::unordered_map<size_t, bool>>& rows);
  size_t total_variables;
};

#endif /* PROBLEM_H_ */

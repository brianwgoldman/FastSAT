/*
 * Problem.h
 *
 *  Created on: Apr 4, 2016
 *      Author: goldman
 */

#ifndef PROBLEM_H_
#define PROBLEM_H_

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

// TODO remove always satisfied dfns and dnfs on zero variables.
class Problem {
 public:
  void load(const string& filename);
  void print(std::ostream& out=std::cout) const;

  Knowledge knowledge_propagate();
  Knowledge knowledge_propagate(const Knowledge& knowledge, bool modify_in_place);

  void assume_and_learn();


  std::unordered_set<std::shared_ptr<DNF>> dnfs;
  vector<weak_dnf_set> variable_to_dnfs;
  weak_dnf_set requires_assume_and_learn;
  Knowledge global_knowledge;
 private:
  void load_dnf(const string& filename);
  void insert_overlap(const Knowledge& knowledge, weak_dnf_set& open_set) const;
  unordered_set<size_t> add_knowledge(const Knowledge& knowledge);
  Knowledge knowledge_propagate(const Knowledge& knowledge, weak_dnf_set& open_set, bool modify_in_place);
  void remove_dnf(std::weak_ptr<DNF>& weak_dnf);

  size_t total_variables;
};

#endif /* PROBLEM_H_ */

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

#include "DNF.h"

using std::string;

class Problem {
 public:
  void load(const string& filename);
  void print(std::ostream& out=std::cout) const;
  vector<std::shared_ptr<DNF>> dnfs;
 private:
  void load_dnf(const string& filename);

  size_t total_variables;
};

#endif /* PROBLEM_H_ */

/*
 * DNF.h
 *
 *  Created on: Apr 4, 2016
 *      Author: goldman
 */

#ifndef DNF_H_
#define DNF_H_

#include <vector>
using std::vector;
using std::size_t;
#include <iostream>

#include "Knowledge.h"

class DNF {
 public:
  DNF() = default;
  DNF(vector<size_t>& var, vector<vector<bool>>& tab) : variables(var), table(tab) {

  }
  virtual ~DNF() = default;
  void print(std::ostream& out=std::cout) const;
  Knowledge create_knowledge() const;
  bool apply_knowledge(const Knowledge& knowledge);
  const vector<size_t>& get_variables() {
    return variables;
  }
  const vector<vector<bool>>& get_table() {
    return table;
  }
 //private:
  vector<size_t> variables;
  vector<vector<bool>> table;
  void remove_column(size_t i);
};

#endif /* DNF_H_ */

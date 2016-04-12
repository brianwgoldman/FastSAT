// The DNF class stores a single function's truth table,
// such that it knows all variables the function uses and
// stores a row for each "true" assignment of those variables
#ifndef DNF_H_
#define DNF_H_

#include <vector>
using std::vector;
using std::size_t;
#include <iostream>

#include "Knowledge.h"

// TODO Consider switching from "row x column to column x row"
class DNF {
 public:
  DNF() = default;
  DNF(vector<size_t>& var, vector<vector<bool>>& tab) : variables(var), table(tab) {

  }
  void print(std::ostream& out=std::cout) const;
  Knowledge create_knowledge() const;
  Knowledge create_knowledge_alternate() const;
  bool apply_knowledge(const Knowledge& knowledge);
  const vector<size_t>& get_variables() {
    return variables;
  }
  const vector<vector<bool>>& get_table() {
    return table;
  }
  static DNF merge(const DNF& a, const DNF& b);
 private:
  vector<size_t> variables;
  vector<vector<bool>> table;
  void remove_column(size_t i);
};

#endif /* DNF_H_ */

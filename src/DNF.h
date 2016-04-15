// The DNF class stores a single function's truth table,
// such that it knows all variables the function uses and
// stores a row for each "true" assignment of those variables
#ifndef DNF_H_
#define DNF_H_

#include <vector>
using std::vector;
using std::size_t;
#include <iostream>
#include <unordered_map>
using std::unordered_map;

#include "Knowledge.h"

const char EITHER=2;

// TODO Consider switching from "row x column to column x row"
// TODO Consider including an algorithm to compress rows using "EITHER"
class DNF {
 public:
  DNF() = default;
  DNF(vector<size_t>& var, vector<vector<char>>& tab) : variables(var), table(tab) {

  }
  DNF(const vector<unordered_map<size_t, bool>>& rows);
  void print(std::ostream& out=std::cout) const;
  Knowledge create_knowledge() const;
  Knowledge create_knowledge_alternate() const;
  bool apply_knowledge(const Knowledge& knowledge);
  const vector<size_t>& get_variables() {
    return variables;
  }
  const vector<vector<char>>& get_table() {
    return table;
  }
  vector<unordered_map<size_t, bool>> convert_to_map() const;
  static DNF merge(const DNF& a, const DNF& b);
 private:
  vector<size_t> variables;
  vector<vector<char>> table;
  void remove_column(size_t i);
};

vector<unordered_map<size_t, bool>> map_merge(vector<unordered_map<size_t, bool>>& a, vector<unordered_map<size_t, bool>>& b);
bool no_growth_map_merge(vector<unordered_map<size_t, bool>>& a, vector<unordered_map<size_t, bool>>& b, vector<unordered_map<size_t, bool>>& result);

#endif /* DNF_H_ */

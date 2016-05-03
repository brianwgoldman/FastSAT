/*
 * Decomposition.h
 *
 *  Created on: Apr 25, 2016
 *      Author: goldman
 */

#ifndef DECOMPOSITION_H_
#define DECOMPOSITION_H_
#include "DNF.h"


class Decomposition {
 public:
  Decomposition(const vector<vector<char>>& t, size_t column);
  double entropy_of_split(size_t split_column) const;
  bool perfectly_decomposed() const;
  void split(size_t split_column);
  DNF create_dnf(const vector<size_t>& column_to_variable) const;
  size_t total_groups() const {
    return end_of_group.size();
  }
  size_t total_rows() const {
    return table.size();
  }
  void print(std::ostream& out = std::cout) const;
  static vector<DNF> decompose(const DNF& dnf, const size_t target, const unordered_set<size_t>& free_variables={});
  static vector<DNF> full_decompose(const DNF& dnf, vector<size_t> priority_order);
 private:
  const vector<vector<char>> table;
  vector<size_t> row_pointers;
  vector<size_t> end_of_group;
  vector<size_t> split_on;
  size_t target_column;
};

template <class T>
double entropy(T& counts, size_t sum_count) {
  double total=0;
  double divisor = static_cast<double>(sum_count);
  for (const auto c : counts) {
    if (c > 0) {
      double p = c / divisor;
      total -= p * log2(p);
    }
  }
  return total;
}

vector<vector<char>> combine_identical(const vector<vector<char>>& table, const size_t column);

#endif /* DECOMPOSITION_H_ */

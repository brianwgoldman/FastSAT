/*
 * Decomposition.cpp
 *
 *  Created on: Apr 25, 2016
 *      Author: goldman
 */

#include "Decomposition.h"
#include <cmath>
#include <array>
using std::array;


// TODO Remove
//#include <iostream>
//using std::cout;
using std::endl;


Decomposition::Decomposition(const vector<vector<char>>& t, size_t column) : table(combine_identical(t, column)) {
  target_column = column;
  row_pointers.resize(table.size());
  // Intially all rows are in one group
  iota(row_pointers.begin(), row_pointers.end(), 0);
  end_of_group.push_back(table.size());
}

double Decomposition::entropy_of_split(size_t split_column) const {
  double total_entropy = 0;
  const double total_rows = static_cast<double>(table.size());
  size_t start = 0;
  array<size_t, 2> group_count;
  array<array<size_t, 3>, 2> value_count;
  for (const auto end : end_of_group) {
    // TODO probably can make this better
    group_count[0] = 0;
    group_count[1] = 0;
    value_count[0][0] = 0;
    value_count[0][1] = 0;
    value_count[0][2] = 0;
    value_count[1][0] = 0;
    value_count[1][1] = 0;
    value_count[1][2] = 0;
    for (size_t i=start; i < end; i++) {
      const auto& row = table[row_pointers[i]];
      size_t split_value = row[split_column];
      size_t target_value = row[target_column];
      value_count[split_value][target_value]++;
      group_count[split_value]++;
    }
    for (size_t i=0; i < 2; i++) {
      total_entropy += (group_count[i] / total_rows) * entropy(value_count[i], group_count[i]);
    }
    // advance start
    start = end;
  }
  return total_entropy;
}

bool Decomposition::perfectly_decomposed() const {
  size_t start = 0;
  for (const auto end : end_of_group) {
    auto value = table[row_pointers[start]][target_column];
    for (size_t i=start+1; i < end; i++) {
      auto other_value = table[row_pointers[i]][target_column];
      if (value != other_value) {
        return false;
      }
    }
    start = end;
  }
  return true;
}

vector<vector<char>> combine_identical(const vector<vector<char>>& table, const size_t column) {
  unordered_map<vector<char>, vector<char>> unique;
  for (auto row : table) {
    // Create a copy of the row without "column" in it
    auto value = row[column];
    std::swap(row[column], row.back());
    row.pop_back();
    // Hash that row
    unique[row].push_back(value);
  }
  vector<vector<char>> new_table;
  for (const auto& pair : unique) {
    // Create a new row from the hashed row
    new_table.push_back(pair.first);
    if (pair.second.size() == 1) {
      // Only one of "table"'s rows hashed here, so just put the value back in.
      new_table.back().push_back(pair.second[0]);
    } else {
      // If two things hit the same bin, fill in with "EITHER"
      new_table.back().push_back(EITHER);
    }
    // put the column back in its rightful place
    std::swap(new_table.back().back(), new_table.back()[column]);
  }
  return new_table;
}

void Decomposition::print(std::ostream& out) const {
  size_t start=0;
  out << "Splitting " << target_column << " using columns: ";
  for (const auto var : split_on) {
    out << var << " ";
  }
  out << endl;
  for (const auto end : end_of_group) {
    out << "Start group" << endl;
    for (size_t i=start; i < end; i++) {
      out << "\t";
      for (const auto value : table[row_pointers[i]]) {
        out << DNF::Printable_Value[value] << " ";
      }
      out << endl;
    }
    start = end;
  }
}

vector<DNF> Decomposition::decompose(const DNF& dnf, const size_t target_variable, const unordered_set<size_t>& free_variables) {
  // Find which column "target_variable" is
  const auto& variables = dnf.get_variables();
  size_t target_column = -1;
  for (size_t c=0; c < variables.size(); c++) {
    if (variables[c] == target_variable) {
      target_column = c;
      break;
    }
  }
  assert(target_column < variables.size());

  Decomposition decomposed(dnf.get_table(), target_column);
  vector<size_t> unused_columns;
  for (size_t i=0; i < variables.size(); i++) {
    if (i != target_column) {
      // Handle all of the free splits
      if (free_variables.count(variables[i])) {
        // TODO Consider only splitting on free variables if not already perfectly partitioned
        if (not decomposed.perfectly_decomposed()) {
          decomposed.split(i);
        }
      } else {
        unused_columns.push_back(i);
      }
    }
  }
  while (not decomposed.perfectly_decomposed() and unused_columns.size() > 0) {
    assert(decomposed.total_groups() < decomposed.total_rows());
    // Find the best split
    size_t best_index = 0;
    double best_entropy = decomposed.entropy_of_split(unused_columns[best_index]);
    for (size_t i=1; i < unused_columns.size(); i++) {
      double test_entropy = decomposed.entropy_of_split(unused_columns[i]);
      if (test_entropy < best_entropy) {
        best_entropy = test_entropy;
        best_index = i;
      }
    }
    // select and remove that column from "unused_columns"
    size_t best_column = unused_columns[best_index];
    std::swap(unused_columns[best_index], unused_columns.back());
    unused_columns.pop_back();
    decomposed.split(best_column);
  }

  if (unused_columns.size() == 0 or decomposed.total_groups() == decomposed.total_rows()) {
    // Requires all of the variables or all rows, so just return
    return vector<DNF>(1, dnf);
  }
  vector<DNF> result;
  result.push_back(decomposed.create_dnf(dnf.get_variables()));
  result.push_back(dnf.without_variable(target_variable));
  return result;
}

vector<DNF> Decomposition::full_decompose(const DNF& dnf, vector<size_t> priority_order) {
  vector<DNF> result;
  assert(not dnf.is_always_sat());
  result.push_back(dnf);
  // Try to split on each variable in the priority order
  for (const auto v : priority_order) {
    auto split = decompose(result.back(), v);
    // Remove what used to be the back and put on the new stuff
    result.pop_back();
    for (const auto& s : split) {
      // TODO Consider the case where the first element of the split is always sat.
      result.push_back(s);
    }
    if (result.back().is_always_sat()) {
      // You decomposed until you got something that is always sat, so stop
      result.pop_back();
      break;
    }
  }
  return result;
}

void Decomposition::split(size_t split_column) {
  split_on.push_back(split_column);
  vector<size_t> new_ends;
  size_t start = 0;
  for (const auto end : end_of_group) {
    assert(end > 0);
    size_t end_falses = end;
    for (size_t i=start; i < end_falses; i++) {
      // If row_pointers[i] points at a row where this column is true
      if (table[row_pointers[i]][split_column]) {
        // make falses end one sooner
        end_falses--;
        std::swap(row_pointers[i], row_pointers[end_falses]);
        i--;
      }
    }
    if (start != end_falses) {
      // Only add "end_falses" if there actually were some falses
      new_ends.push_back(end_falses);
    }
    if (end_falses != end) {
      // Only add "end" if there was some trues
      new_ends.push_back(end);
    }
    // Advance start
    start = end;
  }
  // Splitting cannot make fewer groups
  assert(end_of_group.size() <= new_ends.size());

  // Replace ends with the new ends
  std::swap(end_of_group, new_ends);
}

DNF Decomposition::create_dnf(const vector<size_t>& column_to_variable) const {
  vector<vector<char>> new_table;
  vector<size_t> columns = split_on;
  columns.push_back(target_column);
  size_t start=0;
  for (const auto end : end_of_group) {
    // Build the row corresponding to this group
    new_table.emplace_back();
    for (const auto column : columns) {
      new_table.back().push_back(table[row_pointers[start]][column]);
    }
    // The last column is always the target_column, which is the only one with "EITHER"
    if (new_table.back().back() == EITHER) {
      // make this row false
      new_table.back().back() = false;
      // duplicate it
      new_table.push_back(new_table.back());
      // make this row true
      new_table.back().back() = true;
    }
    // This is assert checking only
    for (size_t i=start+1; i < end; i++) {
      for (const auto column : columns) {
        assert(table[row_pointers[i]][column] == table[row_pointers[start]][column]);
      }
    }
    // End assert checking
    start = end;
  }
  assert(start == table.size());
  vector<size_t> new_variables;
  for (const auto column : columns) {
    new_variables.push_back(column_to_variable.at(column));
  }
  return DNF(new_variables, new_table);
}

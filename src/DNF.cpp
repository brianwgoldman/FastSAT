/*
 * DNF.cpp
 *
 *  Created on: Apr 4, 2016
 *      Author: goldman
 */

#include "DNF.h"
using std::endl;
#include <algorithm>
using std::find;
#include <unordered_map>
using std::unordered_map;

void DNF::print(std::ostream& out) const {
  if (variables.size() == 0) {
    out << "(Empty DNF)" << endl;
    return;
  }
  for (const auto var : variables) {
    out << var << " ";
  }
  out << endl;
  for (const auto& row : table) {
    for (const auto bit : row) {
      out << bit << " ";
    }
    out << endl;
  }
  out << endl;
}

Knowledge DNF::create_knowledge() const {
  Knowledge knowledge;
  if (table.size() == 0) {
    knowledge.is_unsat = true;
    return knowledge;
  }
  assert(variables.size() > 0 or table.size() == 1);
  size_t total_variables = variables.size();
  for (size_t i=0; i < total_variables; i++) {
    // The bool in this pair is if the relationship is "negated"
    vector<std::pair<size_t, bool>> consistent;
    for (size_t j=i+1; j < total_variables; j++) {
      consistent.emplace_back(j, table[0][i] != table[0][j]);
    }
    size_t sum_of_i = 0;
    for (const auto& row : table) {
      auto value_of_i = row[i];
      sum_of_i += value_of_i;
      for (size_t j=0; j < consistent.size(); j++) {
        auto negated = value_of_i != row[consistent[j].first];
        if (negated != consistent[j].second) {
          // the pattern is broken
          swap(consistent[j], consistent.back());
          consistent.pop_back();
          j--;
        }
      }
    }
    if (sum_of_i == 0) {
      // If "i" was always 0, assign it
      knowledge.add(variables[i], false);
    } else if (sum_of_i == table.size()) {
      // If "i" was always 1, assign it
      knowledge.add(variables[i], true);
    } else {
      // Anything still consistent here is actually consistent
      for (const auto& pair : consistent) {
        knowledge.add(TwoConsistency(variables[i], variables[pair.first], pair.second));
      }
    }
  }

  return knowledge;
}

bool DNF::apply_knowledge(const Knowledge& knowledge) {
  bool change_made = false;

  for (size_t i=0; i < variables.size(); i++) {
    auto assigned_it = knowledge.assigned.find(variables[i]);
    if (assigned_it != knowledge.assigned.end()) {
      change_made = true;
      // Filter
      for (size_t r=0; r < table.size(); r++) {
        if (table[r][i] != assigned_it->second) {
          swap(table[r], table.back());
          table.pop_back();
          r--;
        }
      }
      remove_column(i);
      i--;
      continue;
    }
    auto rewrite_it = knowledge.rewrites.find(variables[i]);
    if (rewrite_it != knowledge.rewrites.end()) {
      change_made = true;
      auto to_it = find(variables.begin(), variables.end(), rewrite_it->second.to);
      if (to_it != variables.end()) {
        // This table includes both parts of a two consistency, so we need to filter
        size_t to_index = to_it - variables.begin();
        for (size_t r=0; r < table.size(); r++) {
          auto negated = table[r][i] != table[r][to_index];
          if (negated != rewrite_it->second.negated) {
            swap(table[r], table.back());
            table.pop_back();
            r--;
          }
        }
        remove_column(i);
        i--;
      }
      else {
        assert(variables[i] != rewrite_it->second.to);
        // it only contains the "from" so no rows are removed
        previously_used_variables.push_back(variables[i]);
        variables[i] = rewrite_it->second.to;
        if (rewrite_it->second.negated) {
          for (size_t r=0; r < table.size(); r++) {
            table[r][i] = not table[r][i];
          }
        }
      }
    }
  }
  return change_made;
}

void DNF::remove_column(size_t col) {
  assert(col < variables.size());
  previously_used_variables.push_back(variables[col]);
  // Remove the column header
  std::swap(variables[col], variables.back());
  variables.pop_back();

  for (auto & row : table) {
    swap(row[col], row.back());
    row.pop_back();
  }
}

vector<bool> extract_key(const vector<size_t>& variables_in_key, const unordered_map<size_t, size_t>& var_to_col, const vector<bool>& row) {
  vector<bool> key;
  for (const auto v : variables_in_key) {
    key.push_back(row[var_to_col.at(v)]);
  }
  return key;
}

DNF DNF::merge(const DNF& a, const DNF& b) {
  // Construct variable to column mappings for both functions
  unordered_map<size_t, size_t> var_to_col_a, var_to_col_b;
  for (size_t i=0; i < a.variables.size(); i++) {
    var_to_col_a[a.variables[i]] = i;
  }
  for (size_t i=0; i < b.variables.size(); i++) {
    var_to_col_b[b.variables[i]] = i;
  }

  // Find the set of shared variables
  vector<size_t> shared_var;
  vector<size_t> b_only_var;
  for (const auto v : b.variables) {
    if (var_to_col_a.count(v) == 1) {
      shared_var.push_back(v);
    } else {
      // Only in b
      b_only_var.push_back(v);
    }
  }
  std::unordered_map<vector<bool>, vector<vector<bool>>> key_to_a_rows;
  for (const auto row : a.table) {
    auto key = extract_key(shared_var, var_to_col_a, row);
    key_to_a_rows[key].push_back(row);
  }
  vector<vector<bool>> table;
  for (const auto b_row : b.table) {
    auto key = extract_key(shared_var, var_to_col_b, b_row);
    // Iterate over mergable rows, creating copies
    for (auto new_row : key_to_a_rows[key]) {
      for (const auto v : b_only_var) {
        new_row.push_back(b_row[var_to_col_b[v]]);
      }
      table.push_back(new_row);
    }
  }
  // Create the variable headers
  vector<size_t> variables(a.variables.begin(), a.variables.end());
  variables.insert(variables.end(), b_only_var.begin(), b_only_var.end());
  return DNF(variables, table);
}

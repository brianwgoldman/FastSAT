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
    // Record the relationships between variables in the first row
    for (size_t j=i+1; j < total_variables; j++) {
      consistent.emplace_back(j, table[0][i] != table[0][j]);
    }
    // Check if that relationship is maintained across all rows
    size_t sum_of_i = 0;
    for (const auto& row : table) {
      auto value_of_i = row[i];
      sum_of_i += value_of_i;
      for (size_t j=0; j < consistent.size(); j++) {
        auto negated = value_of_i != row[consistent[j].first];
        if (negated != consistent[j].second) {
          // the pattern is broken, so remove it from "consistent"
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


Knowledge DNF::create_knowledge_alternate() const {
  Knowledge knowledge;
  if (table.size() == 0) {
    knowledge.is_unsat = true;
    return knowledge;
  }
  assert(variables.size() > 0 or table.size() == 1);
  // Create a set of unique patterns to variables
  unordered_map<vector<bool>, std::pair<size_t, bool>> unique;
  const size_t total_variables = variables.size();
  const size_t total_rows = table.size();
  for (size_t i=0; i < total_variables; i++) {
    // The row and its inverse
    vector<bool> key(total_rows);
    vector<bool> neg_key(total_rows);
    size_t sum=0;
    for (size_t r=0; r < total_rows; r++) {
      const auto bit = table[r][i];
      key[r] = bit;
      neg_key[r] = not bit;
      sum += bit;
    }
    if (sum == 0) {
      knowledge.add(variables[i], false);
    } else if (sum == total_rows) {
      knowledge.add(variables[i], true);
    } else {
      auto inserted = unique.insert({key, {variables[i], false}});
      if (inserted.second) {
        // It was unique, so insert the inverse
        unique.insert({neg_key, {variables[i], true}});
      } else {
        // Only get here because something is already in inserted
        auto pair = inserted.first->second;
        knowledge.add(TwoConsistency(variables[i], pair.first, pair.second));
      }
    }
  }
  return knowledge;
}



bool DNF::apply_knowledge(const Knowledge& knowledge) {
  bool change_made = false;
  for (size_t i=0; i < variables.size(); i++) {
    // First check if variable[i] is assigned by this knowledge
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
      // I use a continue here to prevent over-nesting
      continue;
    }
    // Check if variable[i] gets rewritten using this knowledge
    auto rewrite_it = knowledge.rewrites.find(variables[i]);
    if (rewrite_it != knowledge.rewrites.end()) {
      change_made = true;
      // Check if variable[i] rewrites to a variable already in this DNF
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
        variables[i] = rewrite_it->second.to;
        // If the relationship was negated, invert the column
        if (rewrite_it->second.negated) {
          for (auto& row : table) {
            row[i] = not row[i];
          }
        }
      }
    }
  }
  return change_made;
}

void DNF::remove_column(size_t col) {
  assert(col < variables.size());
  // Remove the column header
  std::swap(variables[col], variables.back());
  variables.pop_back();
  // Swap each column to the end and delete it
  for (auto & row : table) {
    swap(row[col], row.back());
    row.pop_back();
  }
}

// This function is used by "merge" but isn't needed outside of this file
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
      // If "v", which we know is in b, is also in a
      shared_var.push_back(v);
    } else {
      // Only in b
      b_only_var.push_back(v);
    }
  }
  // Group rows in "a" by their key
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
      // Add the variables that are only in b
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

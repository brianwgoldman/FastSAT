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

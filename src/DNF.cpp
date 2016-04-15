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

DNF::DNF(const vector<unordered_map<size_t, bool>>& rows) {
  // find all of the variables
  unordered_set<size_t> unique_vars;
  for (const auto& row : rows) {
    for (const auto pair : row) {
      unique_vars.insert(pair.first);
    }
  }
  variables.insert(variables.end(), unique_vars.begin(), unique_vars.end());
  for (const auto& row : rows) {
    table.emplace_back();
    for (const auto v : variables) {
      auto result = row.find(v);
      if (result != row.end()) {
        table.back().push_back(result->second);
      } else {
        table.back().push_back(EITHER);
      }
    }
  }
}

void DNF::print(std::ostream& out) const {
  if (variables.size() == 0) {
    out << "(Empty DNF)" << endl;
    return;
  }
  for (const auto var : variables) {
    out << var << " ";
  }
  out << endl;
  char lookup[] = {'0', '1', '*'};
  for (const auto& row : table) {
    for (const auto bit : row) {
      out << lookup[static_cast<size_t>(bit)] << " ";
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
  // Find all columns that do not contain "EITHER"
  vector<size_t> complete_column;
  size_t total_variables = variables.size();
  for (size_t c=0; c < total_variables; c++) {
    bool found = false;
    for (const auto& row : table) {
      if (row[c] == EITHER) {
        found = true;
        break;
      }
    }
    if (not found) {
      complete_column.push_back(c);
    }
  }


  const size_t total_complete = complete_column.size();
  for (size_t i=0; i < total_complete; i++) {
    const size_t c1 = complete_column[i];
    // The bool in this pair is if the relationship is "negated"
    vector<std::pair<size_t, bool>> consistent;
    // Record the relationships between variables in the first row
    for (size_t j=i+1; j < total_complete; j++) {
      const size_t c2 = complete_column[j];
      consistent.emplace_back(c2, table[0][c1] != table[0][c2]);
    }
    // Check if that relationship is maintained across all rows
    size_t sum_of_c1 = 0;
    for (const auto& row : table) {
      auto value_of_c1 = row[c1];
      sum_of_c1 += value_of_c1;
      for (size_t j=0; j < consistent.size(); j++) {
        auto negated = value_of_c1 != row[consistent[j].first];
        if (negated != consistent[j].second) {
          // the pattern is broken, so remove it from "consistent"
          swap(consistent[j], consistent.back());
          consistent.pop_back();
          j--;
        }
      }
    }
    if (sum_of_c1 == 0) {
      // If "i" was always 0, assign it
      knowledge.add(variables[c1], false);
    } else if (sum_of_c1 == table.size()) {
      // If "i" was always 1, assign it
      knowledge.add(variables[c1], true);
    } else {
      // Anything still consistent here is actually consistent
      for (const auto& pair : consistent) {
        knowledge.add(TwoConsistency(variables[c1], variables[pair.first], pair.second));
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
        if (table[r][i] != assigned_it->second and table[r][i] != EITHER) {
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
          if (table[r][i] != EITHER and table[r][to_index] != EITHER) {
            // The row can only be invalid if both variables have definitive values
            auto negated = table[r][i] != table[r][to_index];
            if (negated != rewrite_it->second.negated) {
              swap(table[r], table.back());
              table.pop_back();
              r--;
            }
          } else if (table[r][to_index] == EITHER and table[r][i] != EITHER) {
            if (rewrite_it->second.negated) {
              table[r][to_index] = not table[r][i];
            } else {
              table[r][to_index] = table[r][i];
            }
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
            if (row[i] != EITHER) {
              row[i] = not row[i];
            }
          }
        }
      }
    }
  }
  // TODO Two rows different by exactly one set variable
  if (change_made) {
    if (table.size() > 0) {
      for (size_t c=0; c < variables.size(); c++) {
        bool all_either = true;
        for (const auto& row : table) {
          if (row[c] != EITHER) {
            all_either = false;
            break;
          }
        }
        if (all_either) {
          remove_column(c);
          c--;
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
    std::swap(row[col], row.back());
    row.pop_back();
  }
}


vector<unordered_map<size_t, bool>> DNF::convert_to_map() const {
  vector<unordered_map<size_t, bool>> result;
  for (const auto & row : table) {
    result.emplace_back();
    for (size_t c=0; c < row.size(); c++) {
      if (row[c] != EITHER) {
        result.back()[variables[c]] = row[c];
      }
    }
  }
  return result;
}

vector<unordered_map<size_t, bool>> map_merge(vector<unordered_map<size_t, bool>>& a, vector<unordered_map<size_t, bool>>& b) {
  vector<unordered_map<size_t, bool>> rows;
  for (const auto row_a : a) {
    for (const auto row_b : b) {
      // Check if they are compatable
      bool compatable = true;
      unordered_map<size_t, bool> new_row(row_b);
      for (const auto pair : row_a) {
        auto result = new_row.insert(pair);
        if (not result.second and result.first->second != pair.second) {
          // If they have different values for this variable
          compatable = false;
          break;
        }
      }
      if (compatable) {
        rows.push_back(new_row);
      }
    }
  }
  return rows;
}

bool no_growth_map_merge(vector<unordered_map<size_t, bool>>& a, vector<unordered_map<size_t, bool>>& b, vector<unordered_map<size_t, bool>>& result) {
  const size_t max_size = a.size() + b.size();
  result.clear();
  for (const auto row_a : a) {
    for (const auto row_b : b) {
      // Check if they are compatable
      bool compatable = true;
      unordered_map<size_t, bool> new_row(row_b);
      for (const auto pair : row_a) {
        auto result = new_row.insert(pair);
        if (not result.second and result.first->second != pair.second) {
          // If they have different values for this variable
          compatable = false;
          break;
        }
      }
      if (compatable) {
        result.push_back(new_row);
        if (result.size() > max_size) {
          return false;
        }
      }
    }
  }
  return true;
}

DNF DNF::merge(const DNF& a, const DNF& b) {
  auto map_a = a.convert_to_map();
  auto map_b = b.convert_to_map();
  auto map_result = map_merge(map_a, map_b);
  return DNF(map_result);
}

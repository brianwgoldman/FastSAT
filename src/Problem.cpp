/*
 * Problem.cpp
 *
 *  Created on: Apr 4, 2016
 *      Author: goldman
 */

#include "Problem.h"
#include <fstream>
using std::ifstream;
#include <sstream>
using std::istringstream;
#include <cassert>
using std::unordered_map;

using std::cout;
using std::endl;

void Problem::load(const string& filename) {
  // clear out the old problem
  dnfs.clear();

  // find the file extension
  size_t dot_position = filename.rfind(".");
  if (dot_position == string::npos) {
    throw std::invalid_argument("Problem file '" + filename + "' missing extension");
  }
  string extension = filename.substr(dot_position + 1);
  if (extension == "dnf") {
    load_dnf(filename);
  } else {
    throw std::invalid_argument("Bad problem file extension: '" + extension + "'");
  }

  // Build variable-to-dnf mapping
  variable_to_dnfs.resize(total_variables + 1);
  for (const auto& dnf : dnfs) {
    for (const auto var : dnf->get_variables()) {
      variable_to_dnfs.at(var).insert(dnf);
    }
  }
  requires_knowledge_propagate.insert(dnfs.begin(), dnfs.end());
  requires_assume_and_learn.insert(dnfs.begin(), dnfs.end());
  sanity_check();
}

void Problem::load_dnf(const string& filename) {
  ifstream in(filename);
  string line, word;
  // Process the header
  getline(in, line);
  istringstream iss(line);
  iss >> word;
  assert(word == "p");
  iss >> word;
  assert(word == "dnf");
  size_t total_dnfs;
  iss >> total_variables >> total_dnfs;
  // Ignore the second line
  getline(in, line);
  vector<vector<bool>> table;

  while (getline(in, line)) {
    istringstream iss(line);
    // If you are starting a new pattern, extract the table
    if (line[0] == '*') {
      table.clear();
      // Throw away the "******* Big integer:"
      iss >> word >> word >> word;
      uint64_t big_int;
      iss >> big_int;
      // Throw away the ", Block size = "
      iss >> word >> word >> word >> word;
      size_t number_of_variables;
      iss >> number_of_variables;

      // While there are set bits in the big integer
      for (size_t position = 0; big_int; position++, big_int>>=1) {

        // If the big integer has a 0 at this position, skip it
        if ((big_int & 1) == 0) {
          continue;
        }
        // Add a row to the table
        table.emplace_back(number_of_variables);
        auto bits = position;
        for (size_t i=0; i < number_of_variables; i++) {
          table.back()[i] = (bits & 1);
          bits >>= 1;
        }
      }
    } else {
      vector<size_t> variables;
      size_t variable;
      while (iss >> variable) {
        assert(0 < variable);
        assert(variable <= total_variables);
        variables.push_back(variable);
      }
      // The number of variables should be equal to the columns in the table
      assert(variables.size() == table[0].size());

      dnfs.insert(std::make_shared<DNF>(variables, table));
    }
  }
  assert(total_dnfs == dnfs.size());
}

void Problem::print(std::ostream& out) const {
  if (dnfs.empty()) {
    out << "(Empy Problem)" << std::endl;
    return;
  }
  for (const auto& dnf : dnfs) {
    dnf->print(out);
  }
}

void Problem::knowledge_propagate() {
  knowledge_propagate(global_knowledge, true);
}

void Problem::propagate_assumption(Knowledge& assumption) {
  for (const auto& pair : assumption.assigned) {
    auto& overlapping_dnfs = variable_to_dnfs[pair.first];
    requires_knowledge_propagate.insert(overlapping_dnfs.begin(), overlapping_dnfs.end());
  }
  // Add all dnfs that overlap a 2-consistency to the open_set
  for (const auto& pair : assumption.rewrites) {
    auto& overlapping_dnfs = variable_to_dnfs[pair.first];
    requires_knowledge_propagate.insert(overlapping_dnfs.begin(), overlapping_dnfs.end());
  }
  knowledge_propagate(assumption, false);
}

void Problem::knowledge_propagate(Knowledge& knowledge, bool modify_in_place) {
  while (not requires_knowledge_propagate.empty()) {
    // Select a "random" function from the open_set
    auto weak_dnf = *requires_knowledge_propagate.begin();
    // If that DNF still exists
    if (auto realized_dnf = weak_dnf.lock()) {
      if (not modify_in_place) {
        // Makes a copy
        realized_dnf = std::make_shared<DNF>(*realized_dnf);
      }
      bool change_made = false;
      change_made |= realized_dnf->apply_knowledge(knowledge);
      auto learned = realized_dnf->create_knowledge();
      if (not learned.empty()) {
        auto require_updating = knowledge.add(learned);
        if (knowledge.is_unsat) {
          // Do not go further, just return what made you UNSAT
          return;
        }
        // Open up affected DNFs
        for (const auto v : require_updating) {
          requires_knowledge_propagate.insert(variable_to_dnfs[v].begin(), variable_to_dnfs[v].end());
        }
        if (modify_in_place) {
          clean_up_bins(require_updating);
        }
        //insert_overlap(learned, open_set);
        change_made |= realized_dnf->apply_knowledge(knowledge);
      }
      if (change_made and modify_in_place) {
        // check to see if this function is now always SAT
        size_t maximum_rows = 1 << realized_dnf->variables.size();
        if (realized_dnf->variables.size() == 0 or realized_dnf->table.size() == maximum_rows) {
          // Remove this function entirely from this problem
          remove_dnf(weak_dnf);
        } else {
          requires_assume_and_learn.insert(weak_dnf);
        }
      }
    } else {
      std::cout << "LOCK GET FAILED in knowledge propagate." << std::endl;
    }
    requires_knowledge_propagate.erase(weak_dnf);
  }
  sanity_check();
}

void Problem::remove_dnf(std::weak_ptr<DNF>& weak_dnf) {
  if (auto realized_dnf = weak_dnf.lock()) {
    // Remove it from variable bins
    for (const auto v : realized_dnf->variables) {
      variable_to_dnfs[v].erase(weak_dnf);
    }
    for (const auto& v : realized_dnf->previously_used_variables) {
      variable_to_dnfs[v].erase(weak_dnf);
    }
    requires_assume_and_learn.erase(weak_dnf);
    dnfs.erase(realized_dnf);
  } else {
    std::cout << "LOCK GET FAILED in remove_dnf" << std::endl;
  }
}

void Problem::clean_up_bins(const unordered_set<size_t>& update_required) {
  for (const auto v : update_required) {
    auto assigned_it = global_knowledge.assigned.find(v);
    auto rewrite_it = global_knowledge.rewrites.find(v);
    if (assigned_it != global_knowledge.assigned.end()) {
      // This variable has been assigned, so clear the bin
      variable_to_dnfs[v].clear();
    } else if (rewrite_it != global_knowledge.rewrites.end()) {
      const auto& rewrite = rewrite_it->second;
      auto& moving = variable_to_dnfs[rewrite.from];
      variable_to_dnfs[rewrite.to].insert(moving.begin(), moving.end());
      moving.clear();
    } else {
      cout << "Cleaning a bit that isn't a global rule!" << endl;
      throw "STOP";
    }
  }
}


void Problem::add_knowledge(const Knowledge& knowledge) {
  auto update_required = global_knowledge.add(knowledge);
  for (const auto v : update_required) {
    requires_knowledge_propagate.insert(variable_to_dnfs[v].begin(), variable_to_dnfs[v].end());
  }
  clean_up_bins(update_required);
  knowledge_propagate(global_knowledge, true);
}

void Problem::assume_and_learn() {
  while (not requires_assume_and_learn.empty()) {
    // Select a "random" function from the set
    auto weak_dnf = *requires_assume_and_learn.begin();
    if (auto realized_dnf = weak_dnf.lock()) {
      const auto& variables = realized_dnf->get_variables();
      auto& table = realized_dnf->table;
      bool row_removed = false;
      for (size_t r=0; r < table.size(); r++) {
        // Assume this row is true
        Knowledge assumption;

        for (size_t i=0; i < variables.size(); i++) {
          assumption.add(variables[i], table[r][i]);
        }
        propagate_assumption(assumption);
        if (assumption.is_unsat) {
          swap(table[r], table.back());
          table.pop_back();
          r--;
          row_removed = true;
        }
      }
      if (row_removed) {
        // Anything that overlaps this DNF could now potentially have a row removed
        for (const auto& v : variables) {
          requires_assume_and_learn.insert(variable_to_dnfs[v].begin(), variable_to_dnfs[v].end());
        }
        auto learned = realized_dnf->create_knowledge();
        if (not learned.empty()) {
          std::cout << "Learned something new" << std::endl;
          learned.print();
          std::cout << std::endl;
          // TODO you may need to use "updates_required" trick for global+learned
          add_knowledge(learned);
          std::cout << "Total in Global: " << global_knowledge.assigned.size() + global_knowledge.rewrites.size() << std::endl;
          std::cout << std::endl;
          if (global_knowledge.is_unsat) {
            return;
          }
        }
      }
    } else {
      std::cout << "LOCK GET FAILED in assume-and-learn" << std::endl;
    }
    requires_assume_and_learn.erase(weak_dnf);
  }
  sanity_check();
}

vector<bool> extract_key(const vector<size_t>& variables_in_key, const unordered_map<size_t, size_t>& var_to_col, const vector<bool>& row) {
  vector<bool> key;
  for (const auto v : variables_in_key) {
    key.push_back(row[var_to_col.at(v)]);
  }
  return key;
}

void Problem::merge(std::weak_ptr<DNF>& weak_a, std::weak_ptr<DNF>& weak_b) {
  auto realized_a=weak_a.lock();
  auto realized_b=weak_b.lock();
  if (realized_a and realized_b) {
    // Construct variable to column mappings for both functions
    unordered_map<size_t, size_t> var_to_col_a, var_to_col_b;
    for (size_t i=0; i < realized_a->variables.size(); i++) {
      var_to_col_a[realized_a->variables[i]] = i;
    }
    for (size_t i=0; i < realized_b->variables.size(); i++) {
      var_to_col_b[realized_b->variables[i]] = i;
    }

    // Find the set of shared variables
    vector<size_t> shared_var;
    vector<size_t> b_only_var;
    for (const auto v : realized_b->variables) {
      if (var_to_col_a.count(v) == 1) {
        shared_var.push_back(v);
      } else {
        // Only in b
        b_only_var.push_back(v);
      }
    }
    std::unordered_map<vector<bool>, vector<vector<bool>>> key_to_a_rows;
    for (const auto row : realized_a->table) {
      auto key = extract_key(shared_var, var_to_col_a, row);
      key_to_a_rows[key].push_back(row);
    }
    vector<vector<bool>> table;
    for (const auto b_row : realized_b->table) {
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
    vector<size_t> variables(realized_a->variables.begin(), realized_a->variables.end());
    variables.insert(variables.end(), b_only_var.begin(), b_only_var.end());
    auto new_dnf = std::make_shared<DNF>(variables, table);
  } else {
    std::cout << "LOCK GET FAILED in merge" << std::endl;
  }
}


void Problem::sanity_check() {
  return;
  bool failure = false;
  for (const auto dnf : dnfs) {
    std::weak_ptr<DNF> weak_dnf = dnf;
    // Check that this DNF is in all of the bins it should be
    for (const auto v : dnf->variables) {
      if (variable_to_dnfs[v].count(weak_dnf) == 0) {
        std::cout << "Failed to find DNF in bin: " << v << std::endl;
        dnf->print();
        failure = true;
      }
    }
  }
  // Check that all bins only contain the correct dnfs
  for (size_t v=0; v < variable_to_dnfs.size(); v++) {
    for (const auto weak_dnf : variable_to_dnfs[v]) {
      if(auto realized_dnf = weak_dnf.lock()) {
        const auto& variables = realized_dnf->variables;
        if (std::find(variables.begin(), variables.end(), v) == variables.end()) {
          std::cout << "DNF in bin " << v << " does not contain that variable" << std::endl;
          realized_dnf->print();
          failure = true;
        }
      } else {
        std::cout << "DNF in bin " << v << " has been deleted." << std::endl;
        failure = true;
      }
    }
  }
  // Check that the weak sets don't contain dead things
  for (const auto weak_dnf : requires_knowledge_propagate) {
    if (not weak_dnf.lock()) {
      std::cout << "Dead dnf found in requires_knowledge_propagate" << std::endl;
      failure = true;
    }
  }
  for (const auto weak_dnf : requires_assume_and_learn) {
    if (not weak_dnf.lock()) {
      std::cout << "Dead dnf found in requires_assume_and_learn" << std::endl;
      failure = true;
    }
  }
  assert(not failure);
}

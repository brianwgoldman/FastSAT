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
  requires_assume_and_learn.insert(dnfs.begin(), dnfs.end());
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

void Problem::insert_overlap(const Knowledge& knowledge, weak_dnf_set& open_set) const {
  // Add all dnfs that overlap an assignment to the open_set
  for (const auto& pair : knowledge.assigned) {
    auto& overlapping_dnfs = variable_to_dnfs[pair.first];
    open_set.insert(overlapping_dnfs.begin(), overlapping_dnfs.end());
  }
  // Add all dnfs that overlap a 2-consistency to the open_set
  for (const auto& pair : knowledge.rewrites) {
    auto& overlapping_dnfs = variable_to_dnfs[pair.first];
    open_set.insert(overlapping_dnfs.begin(), overlapping_dnfs.end());
  }
}

Knowledge Problem::knowledge_propagate() {
  weak_dnf_set open_set(dnfs.begin(), dnfs.end());
  Knowledge empty;
  return knowledge_propagate(empty, open_set, true);
}

Knowledge Problem::knowledge_propagate(const Knowledge& knowledge, bool modify_in_place) {
  weak_dnf_set open_set;
  insert_overlap(knowledge, open_set);
  return knowledge_propagate(knowledge, open_set, modify_in_place);
}
Knowledge Problem::knowledge_propagate(const Knowledge& knowledge, weak_dnf_set & open_set, bool modify_in_place) {
  Knowledge new_knowledge;
  auto total_knowledge = knowledge;
  while (not open_set.empty()) {
    // Select a "random" function from the open_set
    auto weak_dnf = *open_set.begin();
    // If that DNF still exists
    if (auto realized_dnf = weak_dnf.lock()) {
      if (not modify_in_place) {
        realized_dnf = std::make_shared<DNF>(*realized_dnf);
      }
      bool change_made = false;
      change_made |= realized_dnf->apply_knowledge(total_knowledge);
      auto learned = realized_dnf->create_knowledge();
      if (not learned.empty()) {
        new_knowledge.add(learned);
        auto require_updating = total_knowledge.add(learned);
        if (total_knowledge.is_unsat) {
          // Do not go further, just return what made you UNSAT
          new_knowledge.is_unsat = true;
          return new_knowledge;
        }
        // Open up affected DNFs
        //insert_overlap(learned, open_set);
        change_made |= realized_dnf->apply_knowledge(total_knowledge);
        for (const auto v : require_updating) {
          open_set.insert(variable_to_dnfs[v].begin(), variable_to_dnfs[v].end());
        }
      }
      if (change_made and modify_in_place) {
        for (const auto& v : realized_dnf->previously_used_variables) {
          variable_to_dnfs[v].erase(weak_dnf);
        }
        realized_dnf->previously_used_variables.clear();
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
    open_set.erase(weak_dnf);
  }
  if (modify_in_place) {
    add_knowledge(total_knowledge);
  }
  return new_knowledge;
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

unordered_set<size_t> Problem::add_knowledge(const Knowledge& knowledge) {
  auto update_required = global_knowledge.add(knowledge);
  // TODO if this ends up being slow, try to make it only do new knowledge
  // that results from the joining of global and new stuff.
  for (const auto& pair : global_knowledge.assigned) {
    variable_to_dnfs[pair.first].clear();
  }
  // Move all things in the "from" bin of a rule to the "to" bin
  for (const auto& pair : global_knowledge.rewrites) {
    const auto& rewrite = pair.second;
    auto& moving = variable_to_dnfs[rewrite.from];
    variable_to_dnfs[rewrite.to].insert(moving.begin(), moving.end());
    moving.clear();
  }
  return update_required;
}

void Problem::assume_and_learn() {
  requires_assume_and_learn.insert(dnfs.begin(), dnfs.end());
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
        auto learned = knowledge_propagate(assumption, false);
        if (learned.is_unsat) {
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
          auto result = knowledge_propagate(learned, true);
          std::cout << "Propagated" << std::endl;
          result.print();

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
}

/*
 * Knowledge.cpp
 *
 *  Created on: Apr 4, 2016
 *      Author: goldman
 */

#include "Knowledge.h"
#include <cassert>
using std::endl;

unordered_set<size_t> Knowledge::add(const size_t variable, const bool value) {
  auto rewrite_it = rewrites.find(variable);
  // If "variable" is currently being rewriten to something else
  // step forward to it and recurse
  if (rewrite_it != rewrites.end()) {
    auto new_variable = rewrite_it->second.to;
    auto new_value = value;
    if (rewrite_it->second.negated) {
      new_value = not new_value;
    }
    // recurse
    return add(new_variable, new_value);
  }
  // Build up the list of everything that can be assigned using this knowledge
  std::vector<std::pair<size_t, bool>> new_assignments;
  new_assignments.emplace_back(variable, value);
  // Find everything that rewrites to "variable"
  auto it = sources.find(variable);
  if (it != sources.end()) {
    // For each thing that can rewrite to this
    for (const auto new_variable : it->second) {
      // TODO might be better to explicitly use iterators here
      auto & rewrite = rewrites[new_variable];
      auto new_value = value;
      if (rewrite.negated) {
        new_value = not value;
      }
      new_assignments.emplace_back(new_variable, new_value);
      // Delete the rule
      rewrites.erase(new_variable);
      // Warning, at this point "rewrite" is invalid
    }
    // Delete the sources for this rule
    sources.erase(it);
  }
  unordered_set<size_t> updated;
  // Integrate assignments, check for UNSAT
  for (const auto assignment : new_assignments) {
    auto result = assigned.insert(assignment);
    if (not result.second) {
      // If you have seen this assignment before
      if (result.first->second != assignment.second) {
        // This new assignment contradicts a previous assignment
        is_unsat = true;
      }
    } else {
      updated.insert(assignment.first);
    }
  }
  return updated;
}

unordered_set<size_t> Knowledge::add(const TwoConsistency& rewrite) {
  if (assigned.count(rewrite.from)) {
    // "from" is already assigned, so assign "to" as well
    auto value = assigned[rewrite.from];
    if (rewrite.negated) {
      value = not value;
    }
    return add(rewrite.to, value);
  } else if (assigned.count(rewrite.to)) {
    // "to" is already assigned, so assign "from" as well
    auto value = assigned[rewrite.to];
    if (rewrite.negated) {
      value = not value;
    }
    return add(rewrite.from, value);
  } else if (rewrites.count(rewrite.from)) {
    // This rule is trying to rewrite the same variable as another rule
    auto & overlap = rewrites[rewrite.from];
    // Combine the two rewrite rule's negations
    bool new_negated = (overlap.negated != rewrite.negated);
    if (overlap.to < rewrite.to) {
      // We want to use the original's "to"
      TwoConsistency updated(rewrite.to, overlap.to, new_negated);
      // Recurse on the new rule
      return add(updated);
    } else if (overlap.to > rewrite.to) {
      // We want to use the new rule's "to"
      TwoConsistency updated(overlap.to, rewrite.to, new_negated);
      // Recurse on the new rule
      return add(updated);
    } else {
      assert(rewrite.to == overlap.to and rewrite.from == overlap.from);
      if (rewrite.negated != overlap.negated) {
        // We have found two rewrite rules that contradict each other
        is_unsat = true;
      }
      return {};
    }
  } else if (rewrites.count(rewrite.to)) {
    // This rule writes to something that itself has a rewrite
    // Assumes "from" is unique"
    auto updated = rewrite;
    auto & overlap = rewrites[rewrite.to];
    // advance the "to"
    updated.to = overlap.to;
    if (overlap.negated) {
      updated.negated = not updated.negated;
    }
    rewrites[updated.from] = updated;
    sources[updated.to].push_back(updated.from);
    return {updated.from};
  } else {
    unordered_set<size_t> has_been_updated;
    // All other cases can be safely handled by this
    // Rules that currently rewrite to "from" (if any), now need to write to "to"
    for (const auto upstream : sources[rewrite.from]) {
      auto& up = rewrites[upstream];
      up.to = rewrite.to;
      // If the new rule includes a negation, invert old rule's pattern
      if (rewrite.negated) {
        up.negated = not up.negated;
      }
      sources[rewrite.to].push_back(upstream);
      // TODO figure out if this is actually needed
      has_been_updated.insert(up.from);
    }
    // "from" is no longer downstream of anything
    sources.erase(rewrite.from);
    // Add the new rule itself
    rewrites[rewrite.from] = rewrite;
    sources[rewrite.to].push_back(rewrite.from);
    has_been_updated.insert(rewrite.from);
    return has_been_updated;
  }
}

unordered_set<size_t> Knowledge::add(const Knowledge& knowledge) {
  is_sat |= knowledge.is_sat;
  is_unsat |= knowledge.is_unsat;
  unordered_set<size_t> has_been_updated;
  // Add each assignment in "knowledge" to "*this"
  for (const auto & assignment : knowledge.assigned) {
    auto result = add(assignment.first, assignment.second);
    has_been_updated.insert(result.begin(), result.end());
  }
  for (const auto & rewrite : knowledge.rewrites) {
    auto result = add(rewrite.second);
    has_been_updated.insert(result.begin(), result.end());
  }
  return has_been_updated;
}

void Knowledge::print(std::ostream& out) const {
  if (is_sat) {
    out << "Proven SAT" << endl;
    return;
  }
  if (is_unsat) {
    out << "Proven UNSAT" << endl;
    return;
  }
  out << "Assigned: " << assigned.size() << endl;
  print_map(assigned, out);
  out << "Two Consistencies: " << rewrites.size() << endl;
  if (rewrites.size() > 0) {
    vector<size_t> froms;
    for (const auto pair : rewrites) {
      froms.push_back(pair.first);
    }
    sort(froms.begin(), froms.end());
    for (const auto from : froms) {
      rewrites.at(from).print(out);
      out << ", ";
    }
    out << endl;
  }
}

void TwoConsistency::print(std::ostream& out) const {
  out << from;
  if (negated) {
    out << "!";
  }
  out << "=" << to;
}

#include <fstream>
using std::ifstream;
using std::ofstream;
#include <sstream>
using std::istringstream;
using std::endl;
#include <unordered_map>
using std::unordered_map;
#include <algorithm>
using std::max;
// TODO Remove
using std::cout;
void apply_to_cnf(const string in_filename, const Knowledge& knowledge, const string out_filename) {
  ifstream in(in_filename);
  string line, word;
  int literal;
  vector<vector<int>> clauses;
  size_t total_variables=0;
  while (getline(in, line)) {
    istringstream iss(line);
    if (line.empty() or line[0] == 'c') {
      continue;
    }
    else if (line[0] == 'p') {
      // Process the header
      iss >> word;
      assert(word == "p");
      iss >> word;
      assert(word == "cnf");
      iss >> total_variables;
      continue;
    }
    // If you got this far, its to process a cnf
    vector<int> clause;
    while (iss >> literal) {
      if (literal != 0) {
        // If the literal is negated, having a true makes this clause false.
        clause.push_back(literal);
      }
    }
    vector<int> backup = clause;
    assert(literal == 0);
    bool is_sat=false;
    for (size_t i=0; i < clause.size(); i++) {
      size_t variable = abs(clause[i]);
      bool is_true = clause[i] > 0;
      // See if this variable has been assigned
      auto assigned = knowledge.assigned.find(variable);
      auto rewritten = knowledge.rewrites.find(variable);
      if (assigned != knowledge.assigned.end()) {
        if (is_true == assigned->second) {
          is_sat = true;
          break;
        } else {
          // Swap it to the end and remove it
          std::swap(clause[i], clause.back());
          clause.pop_back();
          i--;
        }
      } else if (rewritten != knowledge.rewrites.end()) {
        bool has_both = false;
        for (size_t c=0; c < clause.size(); c++) {
          if (static_cast<size_t>(abs(clause[c])) == rewritten->second.to) {
            has_both = true;
            bool negated = is_true != (clause[c] > 0);
            if (negated != rewritten->second.negated) {
              is_sat = true;
              break;
            }
            break;
          }
        }
        if (not has_both) {
          clause[i] = rewritten->second.to;
          if (is_true == rewritten->second.negated) {
            clause[i] = -clause[i];
          }
        } else {
          std::swap(clause[i], clause.back());
          clause.pop_back();
          i--;
        }
      }
    }
    if (not is_sat) {
      clauses.push_back(clause);
      for (const auto l : clause) {
        assert(static_cast<size_t>(abs(l)) <= total_variables);
      }
      if (clause.size() == 1) {
        for (const auto l : backup) {
          size_t as_var = abs(l);
          if (knowledge.assigned.count(as_var)) {
            cout << "Assigned " << l << " to " << knowledge.assigned.at(as_var) << endl;
          } else if (knowledge.rewrites.count(as_var)) {
            cout << "Rewrote: " << l << " using ";
            knowledge.rewrites.at(as_var).print(cout);
          }
        }
        cout << "Created UNIT" << endl;
        for (const auto l : backup) {
          cout << l << " ";
        }
        cout << endl;
        for (const auto l : clause) {
          cout << l << " ";
        }
        cout << endl;
        throw "STOP";
      }
    }
  }
  /*
  // Put in all of the assignments and 2-consistencies
  for (const auto pair : knowledge.assigned) {
    if (pair.first > total_variables) {
      std::cout << "Assigned DNF auxilary variable" << std::endl;
      continue;
    }
    int literal = pair.first;
    if (not pair.second) {
      literal = -literal;
    }
    clauses.push_back({literal});
  }
  for (const auto pair : knowledge.rewrites) {
    if (pair.first > total_variables or pair.second.to > total_variables) {
      std::cout << "Rewrote from/to DNF auxilary variable" << std::endl;
      continue;
    }
    int from = pair.second.from;
    int to = pair.second.to;
    if (pair.second.negated) {
      to = -to;
    }
    clauses.push_back({from, -to});
    clauses.push_back({-from, to});
  }
  */

  ofstream out(out_filename);
  out << "c Post reductions of " << in_filename << endl;
  out << "p cnf " << total_variables << " " << clauses.size() << endl;
  for (const auto clause : clauses) {
    for (const auto l : clause) {
      out << l << " ";
    }
    out << "0" << endl;
  }
}

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
#include <map>
using std::map;

using std::cout;
using std::endl;
using std::shared_ptr;

#include <math.h>
// TODO Functions can lose variables due to all *, which won't get updated in the bins

void Problem::load(const string& filename) {
  // clear out the old problem
  dnfs.clear();
  variable_to_dnfs.clear();
  requires_knowledge_propagate.clear();
  requires_assume_and_learn.clear();
  global_knowledge = Knowledge();

  // find the file extension
  size_t dot_position = filename.rfind(".");
  if (dot_position == string::npos) {
    throw std::invalid_argument("Problem file '" + filename + "' missing extension");
  }
  string extension = filename.substr(dot_position + 1);
  // TODO Write a loading method for cnf form
  if (extension == "dnf") {
    load_dnf(filename);
  } else if (extension == "cnf" or extension == "dimacs") {
    load_cnf(filename);
  } else {
    throw std::invalid_argument("Bad problem file extension: '" + extension + "'");
  }

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
  variable_to_dnfs.resize(total_variables + 1);
  // Ignore the second line
  getline(in, line);
  vector<vector<char>> table;

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
        table.emplace_back(number_to_row(position, number_of_variables));
      }
    } else {
      // Build up the variables to go with the table
      vector<size_t> variables;
      size_t variable;
      while (iss >> variable) {
        assert(0 < variable);
        assert(variable <= total_variables);
        variables.push_back(variable);
      }
      // The number of variables should be equal to the columns in the table
      assert(variables.size() == table[0].size());
      add_dnf(std::make_shared<DNF>(variables, table));
    }
  }
  assert(total_dnfs == dnfs.size());
}

void Problem::load_cnf(const string& filename) {
  ifstream in(filename);
  string line, word;
  size_t total_functions;
  int literal;
  size_t loaded_functions = 0;
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
      iss >> total_variables >> total_functions;
      variable_to_dnfs.resize(total_variables + 1);
      continue;
    }
    // If you got this far, its to process a cnf
    assert(total_variables > 0 and variable_to_dnfs.size() == total_variables+1);
    vector<size_t> variables;
    vector<char> false_pattern;
    while (iss >> literal) {
      if (literal != 0) {
        // If the literal is negated, having a true makes this clause false.
        false_pattern.push_back(literal < 0);
        if (literal < 0) {
          literal = -literal;
        }
        assert(literal > 0 and static_cast<size_t>(literal) <= total_variables);
        variables.push_back(literal);
      }
    }
    assert(literal == 0);
    size_t limit = 1 << variables.size();
    vector<vector<char>> table;
    for (size_t i=0; i < limit; i++) {
      table.emplace_back(number_to_row(i, variables.size()));
      if (table.back() == false_pattern) {
        table.pop_back();
      }
    }
    assert(table.size() == limit - 1);
    auto made = std::make_shared<DNF>(variables, table);
    add_dnf(made);
    loaded_functions++;
    //std::weak_ptr<DNF> weak_dnf = made;
    //resolve_overlaps(weak_dnf);
  }
  assert(loaded_functions == total_functions);
}

void Problem::print(std::ostream& out) const {
  if (dnfs.empty()) {
    out << "(Empy Problem)" << std::endl;
    return;
  }
  for (const auto& dnf : dnfs) {
    dnf->print_short(out);
    dnf->print(out);
  }
}
void Problem::print_short(std::ostream& out) const {
  out << "Variables: " << total_variables
      << " Assigned: " << global_knowledge.assigned.size()
      << " Rewritten: " << global_knowledge.rewrites.size()
      << " Functions: " << dnfs.size();
  size_t total_rows = 0;
  for (const auto dnf : dnfs) {
    total_rows += dnf->get_table().size();
  }
  out << " Rows: " << total_rows;
  size_t real_variables=0;
  for (const auto& bin : variable_to_dnfs) {
    real_variables += (bin.size() > 1);
  }
  out << " Real Variables: " << real_variables << std::endl;
}

void Problem::knowledge_propagate() {
  // Redirects to the private function saying we want to add to the global knowledge
  // and we want to modify the problem using what we learn
  knowledge_propagate(global_knowledge, true);
}

void Problem::propagate_assumption(Knowledge& assumption) {
  // We need to add all variables in the assumption to "requires_knowledge_propagation"
  for (const auto& pair : assumption.assigned) {
    auto& overlapping_dnfs = variable_to_dnfs[pair.first];
    requires_knowledge_propagate.insert(overlapping_dnfs.begin(), overlapping_dnfs.end());
  }
  // Add all dnfs that overlap a 2-consistency to the open_set
  for (const auto& pair : assumption.rewrites) {
    // TODO technically when not modifying in place, you only need to propagate functions
    // that have both the "from" and the "to" of a 2-consistency.
    auto& overlapping_dnfs = variable_to_dnfs[pair.first];
    requires_knowledge_propagate.insert(overlapping_dnfs.begin(), overlapping_dnfs.end());
  }
  knowledge_propagate(assumption, false);
}

void Problem::knowledge_propagate(Knowledge& knowledge, bool modify_in_place) {
  while (not requires_knowledge_propagate.empty()) {
    //cout << "Top of loop: " << requires_knowledge_propagate.size() << endl;
    // Dump everything into a buffer so that you process everything once before repeating anything
    vector<std::weak_ptr<DNF>> buffer(requires_knowledge_propagate.begin(), requires_knowledge_propagate.end());
    requires_knowledge_propagate.clear();
    while (buffer.size() > 0) {
      auto weak_dnf = buffer.back();
      buffer.pop_back();
      if (not weak_dnf.lock()) {
        // TODO REMOVE THIS
        continue;
      }
      if (modify_in_place) {
        //weak_dnf = resolve_overlaps(weak_dnf);
      }
      auto realized_dnf = weak_dnf.lock();

      assert(realized_dnf);
      if (not modify_in_place) {
        // Makes a copy
        realized_dnf = std::make_shared<DNF>(*realized_dnf);
      }
      // Apply the current knowledge to this dnf
      bool change_made = false;
      change_made |= realized_dnf->apply_knowledge(knowledge);
      // Learn from the (potentially changed) dnf
      auto learned = realized_dnf->create_knowledge();
      if (not learned.empty()) {
        auto require_updating = knowledge.add(learned);
        if (knowledge.is_unsat) {
          // Do not go further, just return what made you UNSAT
          return;
        }
        // Open up affected DNFs
        for (const auto v : require_updating) {
          // TODO Technically if you aren't modify_in_place, you don't need to reopen everything
          requires_knowledge_propagate.insert(variable_to_dnfs[v].begin(), variable_to_dnfs[v].end());
        }
        if (modify_in_place) {
          // This updates "variable_to_dnf"
          clean_up_bins(require_updating);
        }
        // This removes some columns of the dnf now that we know their knowledge
        change_made |= realized_dnf->apply_knowledge(knowledge);
      }
      if (change_made and modify_in_place) {
        // check to see if this function is now always SAT
        size_t dnf_variables = realized_dnf->get_variables().size();
        size_t maximum_rows = 1 << dnf_variables;
        if (dnf_variables == 0 or realized_dnf->get_table().size() == maximum_rows) {
          // Remove this function entirely from this problem as it is always satisfied
          remove_dnf(weak_dnf);
        } else {
          requires_assume_and_learn.insert(weak_dnf);
        }
      }
      // We just finished propagating this dnf, so don't do it again
      requires_knowledge_propagate.erase(weak_dnf);
    }
  }
}

void Problem::add_dnf(const std::shared_ptr<DNF>& dnf) {
  if (dnf->is_always_sat()) {
    cout << "Attempted to add an always sat thing, so don't do that" << endl;
    return;
  }
  dnfs.insert(dnf);
  std::weak_ptr<DNF> weak_dnf = dnf;
  for (const auto v : dnf->get_variables()) {
    variable_to_dnfs[v].insert(weak_dnf);
  }
  requires_knowledge_propagate.insert(weak_dnf);
  requires_assume_and_learn.insert(weak_dnf);
}

void Problem::remove_dnf(std::weak_ptr<DNF> weak_dnf) {
  auto realized_dnf = weak_dnf.lock();
  assert(realized_dnf);
  // Remove it from variable bins
  for (const auto v : realized_dnf->get_variables()) {
    variable_to_dnfs[v].erase(weak_dnf);
  }
  requires_knowledge_propagate.erase(weak_dnf);
  requires_assume_and_learn.erase(weak_dnf);
  dnfs.erase(realized_dnf);
}

void Problem::clean_up_bins(const unordered_set<size_t>& update_required) {
  weak_dnf_set need_cleaning;
  for (const auto v : update_required) {
    auto assigned_it = global_knowledge.assigned.find(v);
    auto rewrite_it = global_knowledge.rewrites.find(v);
    if (assigned_it != global_knowledge.assigned.end()) {
      // This variable has been assigned, so clear the bin
      need_cleaning.insert(variable_to_dnfs[v].begin(), variable_to_dnfs[v].end());
      variable_to_dnfs[v].clear();
    } else if (rewrite_it != global_knowledge.rewrites.end()) {
      // This variable has been rewritten, so move the contents of its bin
      const auto& rewrite = rewrite_it->second;
      auto& moving = variable_to_dnfs[rewrite.from];
      need_cleaning.insert(moving.begin(), moving.end());
      variable_to_dnfs[rewrite.to].insert(moving.begin(), moving.end());
      moving.clear();
    } else {
      cout << "Cleaning a bit that isn't a global rule!" << endl;
      assert(false);
    }
  }
  for (auto weak_dnf : need_cleaning) {
    auto realized_dnf = weak_dnf.lock();
    if (not realized_dnf) {
      // TODO FIX THIS
      continue;
    }
    assert(realized_dnf);
    realized_dnf->apply_knowledge(global_knowledge);
  }
  for (auto weak_dnf : need_cleaning) {
    auto realized_dnf = weak_dnf.lock();
    if (not realized_dnf) {
      // TODO FIX THIS
      continue;
    }
    size_t dnf_variables = realized_dnf->get_variables().size();
    size_t maximum_rows = 1 << dnf_variables;
    if (dnf_variables == 0 or realized_dnf->get_table().size() == maximum_rows) {
      // Remove this function entirely from this problem as it is always satisfied
      remove_dnf(weak_dnf);
    } else {
      //weak_dnf = resolve_overlaps(weak_dnf);
      requires_knowledge_propagate.insert(weak_dnf);
      requires_assume_and_learn.insert(weak_dnf);
    }
  }
}


void Problem::add_knowledge(const Knowledge& knowledge) {
  auto update_required = global_knowledge.add(knowledge);
  // Figure out which dnfs are directly affected by the new knowledge
  clean_up_bins(update_required);
  // propagate the new knowledge
  knowledge_propagate(global_knowledge, true);
}


std::shared_ptr<DNF> Problem::simple_convert(vector<unordered_map<size_t, bool>>& rows) {
  vector<size_t> universal;
  assert(rows.size() > 0);
  for (const auto pair : rows[0]) {
    universal.emplace_back(pair.first);
  }
  for (size_t r=1; r < rows.size(); r++) {
    for (size_t i=0; i < universal.size(); i++) {
      // If this "universal" variable isn't in row "r"
      if (rows[r].count(universal[i]) == 0) {
        std::swap(universal[i], universal.back());
        universal.pop_back();
        i--;
      }
    }
  }
  vector<vector<char>> table;
  for (const auto row : rows) {
    vector<char> table_row;
    for (const auto v : universal) {
      table_row.push_back(row.at(v));
    }
    table.push_back(table_row);
  }
  return std::make_shared<DNF>(universal, table);
}


std::shared_ptr<DNF> Problem::smart_convert(vector<unordered_map<size_t, bool>>& rows) {
  // This function is like the other "convert"s, except it also tries to repair off-by-one variables
  unordered_map<size_t, size_t> frequency;

  // Figure out how often each variable appears
  for (const auto & row : rows) {
    for (const auto pair : row) {
      frequency[pair.first]++;
    }
  }
  unordered_set<size_t> universal;
  unordered_set<size_t> unprocessed;
  // Add everything to unprocessed
  for (const auto pair : frequency) {
    unprocessed.insert(pair.first);
  }
  while (not unprocessed.empty()) {
    auto variable_it = unprocessed.begin();
    auto variable = *variable_it;
    unprocessed.erase(variable_it);
    size_t seen = frequency[variable];
    if (seen == rows.size()) {
      universal.insert(variable);
    } else if (seen == rows.size() - 1 and rows.size() < 1000) {
      // Find the first variable that appears in all but one row
      // Find the row that doesn't have this variable
      size_t missing;
      for (size_t i=0; i < rows.size(); i++) {
        if (rows[i].count(variable) == 0) {
          missing = i;
        }
      }
      // Build up the two knowledges
      Knowledge with_zero;
      for (const auto pair : rows[missing]) {
        with_zero.add(pair.first, pair.second);
      }
      Knowledge with_one = with_zero;
      with_zero.add(variable, false);
      with_one.add(variable, true);
      propagate_assumption(with_zero);
      propagate_assumption(with_one);
      // remove the old row
      swap(rows[missing], rows.back());
      auto old_row = rows.back();

      rows.pop_back();
      if (not with_zero.is_unsat) {
        if (with_one.is_unsat) {
          // If only "with_zero" is sat
          for (const auto pair : with_zero.assigned) {
            if (old_row.count(pair.first) == 0) {
              frequency[pair.first]++;
              unprocessed.insert(pair.first);
            }
          }
          cout << "Added 0" << endl;
          rows.push_back(with_zero.assigned);
        } else {
          // both versions were still satisfiable, so combine their knowledge
          for (const auto pair : with_zero.assigned) {
            auto result = with_one.assigned.find(pair.first);
            if (result != with_one.assigned.end() and result->second == pair.second) {
              auto inserted = old_row.insert(pair);
              if (inserted.second) {
                cout << "Inserted!" << endl;
                frequency[pair.first]++;
              }
            }
          }
          rows.push_back(old_row);
        }
      } else if (not with_one.is_unsat) {
        // If only "with_one" is sat
        for (const auto pair : with_one.assigned) {
          if (old_row.count(pair.first) == 0) {
            frequency[pair.first]++;
            unprocessed.insert(pair.first);
          }
        }
        cout << "Added 1" << endl;
        rows.push_back(with_one.assigned);
      }
      if (with_zero.is_unsat and with_one.is_unsat) {
        cout << "Both unsat, reopening everything" << endl;
        for (auto & pair : frequency) {
          if (old_row.count(pair.first)) {
            // You don't get counted in this row, but that can't change if you needed to be processed.
            pair.second--;
          } else {
            // You weren't in this row, so it might be necessary
            unprocessed.insert(pair.first);
          }
        }
      }
    }
  }
  vector<size_t> ordered_universal(universal.begin(), universal.end());
  vector<vector<char>> table;
  for (const auto row : rows) {
    vector<char> table_row;
    for (const auto v : ordered_universal) {
      table_row.push_back(row.at(v));
    }
    table.push_back(table_row);
  }
  return std::make_shared<DNF>(ordered_universal, table);
}

std::weak_ptr<DNF> Problem::resolve_overlaps(std::weak_ptr<DNF>& weak_dnf) {
  //assert(false);
  //return weak_dnf;
  auto realized_dnf = weak_dnf.lock();
  // TODO remove this
  if (not realized_dnf) {
    return weak_dnf;
  }
  assert(realized_dnf);
  unordered_map<std::shared_ptr<DNF>, size_t> overlap_count;
  // Count how often other dnf overlaps "weak_dnf"
  for (const auto v : realized_dnf->get_variables()) {
    for (const auto& weak_overlap : variable_to_dnfs[v]) {
      // TODO Remove this
      if (not weak_overlap.lock()) {
        continue;
      }
      assert(weak_overlap.lock());
      overlap_count[weak_overlap.lock()]++;
    }
  }
  auto original_map = realized_dnf->convert_to_map();
  // Ensure you don't find yourself
  overlap_count.erase(realized_dnf);
  vector<unordered_map<size_t, bool>> result_map;
  for (const auto pair : overlap_count) {
    auto partner_map = pair.first->convert_to_map();
    bool attempt = no_growth_map_merge(original_map, partner_map, result_map);
    if (attempt) {
      auto result = std::make_shared<DNF>(result_map);
      cout << "Merging " << realized_dnf->get_table().size()
           << "+" << pair.first->get_table().size()
           << "=" << result->get_table().size() << endl;
      std::weak_ptr<DNF> tmp = realized_dnf;
      remove_dnf(tmp);
      tmp = pair.first;
      remove_dnf(tmp);
      add_dnf(result);
      original_map = result->convert_to_map();
      realized_dnf = result;
      weak_dnf = realized_dnf;
    }
  }
  return weak_dnf;
}

shared_ptr<DNF> split_out_fewest_rows(vector<shared_ptr<DNF>> & group) {
  assert(group.size() > 0);
  size_t choice = 0;
  for (size_t i=1; i < group.size(); i++) {
    if (group[choice]->get_table().size() > group[i]->get_table().size()) {
      choice = i;
    }
  }
  std::swap(group[choice], group.back());
  auto result = group.back();
  group.pop_back();
  return result;
}

shared_ptr<DNF> split_out_most_overlap(vector<shared_ptr<DNF>>& group, const shared_ptr<DNF> partner) {
  assert(group.size() > 0);
  unordered_set<size_t> partner_variables(partner->get_variables().begin(), partner->get_variables().end());
  size_t most_overlap = 0;
  size_t choice = 0;
  for (size_t i=0; i < group.size(); i++) {
    size_t overlap = 0;
    for (const auto v : group[i]->get_variables()) {
      overlap += partner_variables.count(v);
    }

    if (overlap > most_overlap) {
      most_overlap = overlap;
      choice = i;
    }
  }
  std::swap(group[choice], group.back());
  auto result = group.back();
  group.pop_back();
  return result;
}

size_t Problem::freeze_variables_and_insert(DNF dnf) {
  cold_storage.push_back(std::make_shared<DNF>(dnf));
  size_t removed = 0;
  auto copy_var = dnf.get_variables();
  for (const auto v : copy_var) {
    if (variable_to_dnfs[v].size() == 0) {
      // TODO Consider a method that doesn't require copies here.
      dnf = dnf.without_variable(v);
      removed++;
    }
  }
  if (removed == 0) {
    // Don't store it unless you actually removed something
    cold_storage.pop_back();
  }
  if (not dnf.is_always_sat()) {
    // TODO Some assurances that if removed == 0 this doesn't create
    // any duplicate DNFs
    add_dnf(std::make_shared<DNF>(dnf));
  }
  return removed;
}

std::shared_ptr<DNF> extract_useful(vector<std::shared_ptr<DNF>>& copy_group, vector<std::shared_ptr<DNF>>& group,
                                    const size_t variable, const unordered_set<size_t>& shared_variables, vector<std::shared_ptr<DNF>>& to_add) {
  while (copy_group.size() > 0) {
    auto fewest = split_out_fewest_rows(copy_group);
    auto split = Decomposition::decompose(*fewest, variable, shared_variables);
    if (split.size() == 2) {
      if (split[1].is_always_sat()) {
        for (auto & dnf : group) {
          if (dnf == fewest) {
            *dnf = split[0];
          }
        }
      } else {
        to_add.push_back(std::make_shared<DNF>(split[1]));
      }
    }
    if (not split[0].is_always_sat()) {
      return std::make_shared<DNF>(split[0]);
    }
  }
  return shared_ptr<DNF>();
}

bool Problem::extract_variable(size_t variable) {
  // Pull all functions that variable is in out of the problem
  vector<std::shared_ptr<DNF>> group;
  for (const auto dnf : variable_to_dnfs[variable]) {
    auto realized = dnf.lock();
    assert(realized);
    assert(not realized->is_always_sat());
    group.push_back(realized);
  }
  for (const auto dnf : group) {
    remove_dnf(dnf);
  }
  if (group.size() == 0) {
    return false;
  } else if (group.size() == 1) {
    auto removed = freeze_variables_and_insert(*group[0]);
    assert(removed > 0);
    return true;
  }
  // The group size is 2 or more
  // Find how often each variable appears in this group
  unordered_map<size_t, size_t> frequency;
  for (const auto dnf : group) {
    for (const auto v : dnf->get_variables()) {
      frequency[v] ++;
    }
  }
  // If a variable appears in at least 2, it is "shared"
  unordered_set<size_t> shared_variables;
  for (const auto pair : frequency) {
    if (pair.second > 1) {
      shared_variables.insert(pair.first);
    }
  }
  // the target variable doesn't count.
  shared_variables.erase(variable);
  auto copy_group = group;
  vector<shared_ptr<DNF>> to_add;
  shared_ptr<DNF> combined = extract_useful(copy_group, group, variable, shared_variables, to_add);
  while (copy_group.size() > 0) {
    shared_ptr<DNF> partner = extract_useful(copy_group, group, variable, shared_variables, to_add);
    if (not partner) {
      // Everything else in the group decomposed to always sat
      break;
    }
    if (combined->get_table().size() * partner->get_table().size() > 10000) {
      // Too big to try the merge
      // TODO consider smarter expected size measures. For instance,
      // if partner is a subset of combined, always merge
      copy_group.push_back(partner);
      break;
    }
    assert(not partner->is_always_sat());
    combined = std::make_shared<DNF>(DNF::merge(*combined, *partner));
    if (combined->is_always_sat()) {
      cout << "You should check for always sat AFTER merge" << endl;
      assert(false);
    }
  }
  if (copy_group.size() == 0) {
    // Successful merge
    auto removed = freeze_variables_and_insert(*combined);
    assert(removed > 0);
    // Put the residuals back into the problem
    for (const auto dnf : to_add) {
      add_dnf(dnf);
    }
    // Assert checking only
    for (const auto dnf : to_add) {
      for (const auto v : dnf->get_variables()) {
        assert(v != variable);
      }
    }
    // End assert checking
    return true;
  } else {
    // Merge failed, so just put the stuff back how it was
    for (const auto dnf : group) {
      add_dnf(dnf);
      // Assume they've already done this
      requires_knowledge_propagate.erase(dnf);
      requires_assume_and_learn.erase(dnf);
    }
    return false;
  }
}

bool Problem::make_singles() {
  bool change_made = false;
  vector<size_t> still_alive(variable_to_dnfs.size());
  iota(still_alive.begin(), still_alive.end(), 0);
  size_t loops=0;
  while (still_alive.size() > 0) {
    loops++;
    if (loops %  1000 == 0) {
      std::cout << "Completed " << loops << " loops of make singles" << endl;
    }
    size_t choice_index=0;
    for (size_t i=1; i < still_alive.size(); i++) {
      if (variable_to_dnfs[still_alive[i]].size() <  2) {
        // Automatically extract anything that is in 1 function
        if (variable_to_dnfs[still_alive[i]].size() == 1) {
          extract_variable(still_alive[i]);
        }
        std::swap(still_alive[i], still_alive.back());
        still_alive.pop_back();
        i--;
        continue;
      }
      // Find the variable in the fewest functions
      if (variable_to_dnfs[still_alive[i]].size() < variable_to_dnfs[still_alive[choice_index]].size()) {
        choice_index = i;
      }
    }
    auto variable = still_alive[choice_index];
    std::swap(still_alive[choice_index], still_alive.back());
    still_alive.pop_back();
    auto success = extract_variable(variable);
    if (success) {
      change_made = true;
      knowledge_propagate();
    }
  }
  return change_made;
}

void Problem::clear_identical() {
  unordered_map<vector<size_t>, vector<shared_ptr<DNF>>> hashed;
  for (const auto dnf : dnfs) {
    auto variables = dnf->get_variables();
    sort(variables.begin(), variables.end());
    hashed[variables].push_back(dnf);
  }
  for (auto& pair : hashed) {
    if (pair.second.size() > 1) {
      cout << "Found identical: " << pair.second.size() << endl;
      auto combined = pair.second.back();
      pair.second.pop_back();
      while (pair.second.size() > 0) {
        auto partner = pair.second.back();
        if (partner->get_table().size() != combined->get_table().size()) {
          cout << "Identical variables, different rows!" << endl;
        }
        pair.second.pop_back();
        combined = merge(combined, partner).lock();
      }
      cout << "Created" << endl;
      combined->print_short();
    }
  }
}

bool Problem::break_down() {
  bool success = false;
  auto unprocessed = dnfs;
  size_t loop = 0;
  while (unprocessed.size() > 0) {
    loop++;
    if (loop % 1000 == 0) {
      cout << "Completed " << loop << " loops of breakdown" << endl;
    }
    // Select an unprocessed dnf
    auto dnf = *unprocessed.begin();
    unprocessed.erase(dnf);
    remove_dnf(dnf);
    // Order the variables based on how many they currently appear in
    auto order = dnf->get_variables();
    sort(order.begin(), order.end(), [this](const size_t& i, const size_t& j) {
         return variable_to_dnfs[i].size() < variable_to_dnfs[j].size();});
    // Decompose based on that order
    auto pieces = Decomposition::full_decompose(*dnf, order);
    success |= (pieces.size() > 1);
    for (const auto piece : pieces) {
      if (not piece.is_always_sat()) {
        auto as_shared = std::make_shared<DNF>(piece);
        add_dnf(as_shared);
        if (pieces.size() > 1) {
          // TODO Determine if reprocessing something that was broken down
          // is actually useful
          unprocessed.insert(as_shared);
        }
      }
    }
  }
  return success;
}

void Problem::equal_variable_assuming() {
  unordered_map<size_t, size_t> variable_tests;
  size_t loops = 0;
  while (not requires_assume_and_learn.empty()) {
    loops++;
    if (loops > 500) {
      return;
    }
    std::shared_ptr<DNF> realized_dnf;
    //std::pair<size_t, double> best_score = {-1, -1};
    std::pair<double, size_t> best_score = {999999999, -1};
    for (const auto weak_new : requires_assume_and_learn) {
      auto realized_new = weak_new.lock();
      if (not realized_new) {
        continue;
      }
      double total_count=0;
      for (const auto v : realized_new->get_variables()) {
        total_count += variable_tests[v];
      }
      //std::pair<size_t, double> new_score = {realized_new->get_table().size(), total_count / realized_new->get_variables().size()};
      std::pair<double, size_t> new_score = {total_count / realized_new->get_variables().size(), realized_new->get_table().size()};
      if (new_score < best_score) {
        best_score = new_score;
        realized_dnf = realized_new;
      }
    }
    cout << "Score: " << best_score.first << " " << best_score.second << endl;
    assert(realized_dnf);
    // Do the assume-and-learn
    realized_dnf = assume_and_learn(realized_dnf);
    //realized_dnf = fill_in_stars(realized_dnf);
    // Mark the variables
    for (const auto v : realized_dnf->get_variables()) {
      variable_tests[v]++;
    }

    auto learned = realized_dnf->create_knowledge();
    if (not learned.empty()) {
      cout << "Learned from the assume-and-learn" << endl;
      learned.print();
      add_knowledge(learned);
    }
    std::weak_ptr<DNF> weak = realized_dnf;
    realized_dnf = resolve_overlaps(weak).lock();
    requires_assume_and_learn.erase(realized_dnf);
    print_short();

  }
}

void Problem::scan_variables() {
  for (size_t v=variable_to_dnfs.size() - 1; v > 0; v--) {
    const auto bin = variable_to_dnfs[v];
    if (bin.size() < 2) {
      continue;
    }
    cout << "Starting variable " << v << endl;
    for (const auto weak_dnf : bin) {
      auto realized_dnf = weak_dnf.lock();
      if (not realized_dnf) {
        continue;
      }
      realized_dnf = assume_and_learn(realized_dnf);
      auto learned = realized_dnf->create_knowledge();
      if (not learned.empty()) {
        cout << "Learned from the assume-and-learn" << endl;
        learned.print();
        add_knowledge(learned);
      }
      std::weak_ptr<DNF> weak = realized_dnf;
      realized_dnf = resolve_overlaps(weak).lock();
      print_short();
      if (global_knowledge.assigned.count(v) != 0 or global_knowledge.rewrites.count(v) != 0) {
        cout << "Learned the variable!" << endl;
        break;
      }
    }
  }
}

std::shared_ptr<DNF> Problem::fill_in_stars(std::shared_ptr<DNF> realized_dnf) {
  if (realized_dnf->get_table().size() >= 64) {
    return realized_dnf;
  }
  //cout << "Filling in with " << realized_dnf->get_table().size() << " rows" << endl;
  size_t best_column = -1;
  size_t star_count = -1;
  bool missing_value = false;
  for (size_t col=0; col < realized_dnf->get_variables().size(); col++) {
    unordered_map<char, size_t> counts;
    for (const auto & row : realized_dnf->get_table()) {
      counts[row[col]]++;
    }
    if (counts.count(EITHER) == 0 or counts.size() == 3) {
      continue;
    }
    // The column only has 1 setting, and its always the same value
    if (counts.at(EITHER) < star_count) {
      star_count = counts.at(EITHER);
      best_column = col;
      missing_value = counts.count(false);
    }
  }
  if (best_column >= realized_dnf->get_variables().size()) {
    return realized_dnf;
  }
  auto variable = realized_dnf->get_variables()[best_column];
  // Find the rows that have EITHER for that column
  auto new_rows = realized_dnf->convert_to_map();
  bool changed = false;
  for (size_t r=0; r < new_rows.size(); r++) {
    if (new_rows[r].count(variable) == 0) {
      // This row doesn't have a value for this variable
      Knowledge assumption;
      assumption.assigned = new_rows[r];
      assumption.add(variable, missing_value);
      propagate_assumption(assumption);
      new_rows[r][variable] = not missing_value;
      if (not assumption.is_unsat) {
        //cout << "Broke Streak" << endl;
        // Add the row back in (and its consequences) only if it didn't lead to a contradiction
        new_rows.push_back(assumption.assigned);
        // Found a row that breaks the uniformity, so stop
        changed=true;
        break;
      } else {
        //cout << "Extended streak" << endl;
        changed = true;
      }
    }
  }
  if (changed) {
    realized_dnf = std::make_shared<DNF>(new_rows);
  }
  //cout << "End of fill in stars" << endl;
  return fill_in_stars(realized_dnf);
}

std::shared_ptr<DNF> Problem::smarter_fill(std::shared_ptr<DNF> realized_dnf) {
  auto new_rows = realized_dnf->convert_to_map();
  for (size_t col=0; col < realized_dnf->get_variables().size(); col++) {
    unordered_map<char, size_t> counts;
    for (const auto & row : realized_dnf->get_table()) {
      counts[row[col]]++;
    }
    if (counts.count(EITHER) == 0 or counts.size() == 3) {
      continue;
    }
    // The column only has 1 setting, and its always the same value
    auto variable = realized_dnf->get_variables()[col];
    bool missing_value = counts.count(false);
    // Find the rows that have EITHER for that column
    for (size_t r=0; r < new_rows.size(); r++) {
      if (new_rows[r].count(variable) == 0) {
        // This row doesn't have a value for this variable
        Knowledge assumption;
        assumption.assigned = new_rows[r];
        assumption.add(variable, missing_value);
        propagate_assumption(assumption);
        if (assumption.is_unsat) {
          cout << "Added" << endl;
          new_rows[r][variable] = not missing_value;
        } else {
          //cout << "Failed" << endl;
        }
      }
    }
  }
  return std::make_shared<DNF>(new_rows);
}

std::shared_ptr<DNF> Problem::assume_and_learn(std::shared_ptr<DNF>& realized_dnf) {
  std::weak_ptr<DNF> weak_dnf = realized_dnf;
  // TODO when you remove smart pointers, you'll need to make this safe again
  remove_dnf(weak_dnf);
  const auto& variables = realized_dnf->get_variables();
  const auto& table = realized_dnf->get_table();
  cout << "Before " << variables.size() << "x" << table.size() << endl;
  vector<unordered_map<size_t, bool>> new_rows;
  for (const auto& row : realized_dnf->convert_to_map()) {
    // Assume this row is true
    Knowledge assumption;
    assumption.assigned = row;
    /*
    for (size_t i=0; i < variables.size(); i++) {
      assumption.add(variables[i], row[i]);
    }
    */
    propagate_assumption(assumption);
    //cout << "After assumption assignments: " << assumption.assigned.size() << " " << assumption.is_unsat << endl;
    if (not assumption.is_unsat) {
      // Add the row back in (and its consequences) only if it didn't lead to a contradiction
      new_rows.push_back(assumption.assigned);

    }
  }
  auto new_dnf = simple_convert(new_rows);
  //auto new_dnf = std::make_shared<DNF>(new_rows);
  //auto new_dnf = smart_convert(new_rows);
  //cout << "Middle " << new_dnf->get_variables().size() << "x" << new_dnf->get_table().size() << endl;
  //new_dnf = smarter_fill(new_dnf);
  cout << "After  " << new_dnf->get_variables().size() << "x" << new_dnf->get_table().size() << endl;
  //new_dnf->print();
  // Add it back into the problem
  add_dnf(new_dnf);
  return new_dnf;
}

void Problem::assume_and_learn() {
  size_t good=0, bad=0;
  unordered_map<std::shared_ptr<DNF>, size_t> count;
  while (not requires_assume_and_learn.empty()) {
    print_short();
    auto realized_dnf = requires_assume_and_learn.begin()->lock();
    assert(realized_dnf);
    //std::pair<size_t, size_t> current_score = {-realized_dnf->get_variables().size(), realized_dnf->get_table().size()};
    //size_t current_score = count[realized_dnf];
    //std::pair<size_t, size_t> current_score = {count[realized_dnf], *min_element(realized_dnf->get_variables().begin(), realized_dnf->get_variables().end())};
    std::pair<size_t, size_t> current_score = {count[realized_dnf], realized_dnf->get_table().size()};
    // Find the "best", this could probably be made more efficient
    for (const auto weak_new : requires_assume_and_learn) {
      auto realized_new = weak_new.lock();
      assert(realized_new);
      //std::pair<size_t, size_t> new_score = {-realized_new->get_variables().size(), realized_new->get_table().size()};
      //size_t new_score = count[realized_new];
      //std::pair<size_t, size_t> new_score = {count[realized_new], *min_element(realized_new->get_variables().begin(), realized_new->get_variables().end())};
      std::pair<size_t, size_t> new_score = {count[realized_new], realized_new->get_table().size()};
      if (current_score > new_score) {
        realized_dnf = realized_new;
        current_score = new_score;
      }
    }
    size_t new_count = count[realized_dnf] + 1;
    count.erase(realized_dnf);
    cout << "COUNT: " << new_count << " good: " << good << " bad: " << bad << endl;
    //cout << "Good: " << good << " bad: " << bad << endl;
    // Temporarily remove it from the problem (will remove it from requires_assume_and_learn)
    auto new_dnf = assume_and_learn(realized_dnf);
    //cout << "After " << new_dnf->get_variables().size() << "x" << new_dnf->get_table().size() << endl;
    //new_dnf->create_knowledge().print();
    //new_dnf = fill_in_stars(new_dnf);
    //cout << "Third " << new_dnf->get_variables().size() << "x" << new_dnf->get_table().size() << endl;
    //new_dnf->create_knowledge().print();
    if (new_dnf->get_variables().size() == realized_dnf->get_variables().size() and
        new_dnf->get_table().size() == realized_dnf->get_table().size()) {
      bad++;
    } else {
      good++;
    }
    // Resolve any subset/superset relationships this new dnf may ave
    std::weak_ptr<DNF> weak_new = new_dnf;
    weak_new = resolve_overlaps(weak_new);
    new_dnf = weak_new.lock();
    count[new_dnf] = new_count;
    // If the variables or the rows changed
    if (new_dnf->get_variables().size() != realized_dnf->get_variables().size() or new_dnf->get_table().size() != realized_dnf->get_table().size()) {
      // Anything that overlaps this DNF could now potentially have a row removed
      //*
      for (const auto v : new_dnf->get_variables()) {
        requires_assume_and_learn.insert(variable_to_dnfs[v].begin(), variable_to_dnfs[v].end());
      }
      //*/
      auto learned = new_dnf->create_knowledge();
      if (not learned.empty()) {
        std::cout << "Learned something new" << std::endl;
        learned.print();
        std::cout << std::endl;
        add_knowledge(learned);
        if (global_knowledge.is_unsat) {
          return;
        }
      }
    }
    requires_assume_and_learn.erase(new_dnf);
  }
  cout << "Good: " << good << " Bad: " << bad << endl;
  print_short();
}

std::weak_ptr<DNF> Problem::merge(std::weak_ptr<DNF> weak_a, std::weak_ptr<DNF> weak_b) {
  auto realized_a = weak_a.lock();
  auto realized_b = weak_b.lock();
  assert(realized_a and realized_b);
  auto realized_new = std::make_shared<DNF>(DNF::merge(*realized_a, *realized_b));
  cout << "Merged: " << realized_a->get_variables().size() << "x" << realized_a->get_table().size()
       << " + " << realized_b->get_variables().size() << "x" << realized_b->get_table().size()
       << " = " << realized_new->get_variables().size() << "x" << realized_new->get_table().size() << endl;
  //realized_a->print();
  //realized_b->print();
  //realized_new->print();
  remove_dnf(weak_a);
  remove_dnf(weak_b);
  add_dnf(realized_new);
  return realized_new;
}


void Problem::sanity_check() {
  bool failure = false;
  for (const auto dnf : dnfs) {
    std::weak_ptr<DNF> weak_dnf = dnf;
    // Check that this DNF is in all of the bins it should be
    for (const auto v : dnf->get_variables()) {
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
        const auto& variables = realized_dnf->get_variables();
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

bool is_superset(const vector<int> & super, const vector<int>& sub) {
  if (sub.size() > super.size()) {
    return false;
  }
  size_t super_it=0;
  for (const auto c : sub) {
    // Go until super's value is a least as big
    while (super_it < super.size() and super[super_it] < c) {
      super_it++;
    }
    // Fail if super had nothing that big, or if it was bigger
    if (super_it >= super.size() or super[super_it] > c) {
      return false;
    }
  }
  return true;
}

void Problem::convert_to_dimacs(const string filename) const {
  // Maps a clause to if it has no subsets
  unordered_map<vector<int>, bool> clauses;
  size_t loop=0;
  for (const auto dnf : dnfs) {
    loop++;
    if (loop%1000 == 0) {
      cout << "Convert to dimacs has completed " << loop << " loops and created "
           << clauses.size() << " clauses " << endl;
    }
    auto unprocessed = dnf->convert_to_cnfs();
    while (unprocessed.size() > 0) {
      auto working = unprocessed.back();
      unprocessed.pop_back();
      auto inserted = clauses.insert({working, true});
      if (not inserted.second) {
        // If you've seen this clause before, skip it
        continue;
      }
      // Try negating one literal at a time to see if that also exists
      for (size_t i=0; i < working.size(); i++) {
        working[i] = -working[i];
        if (clauses.count(working)) {
          // create the clause without that literal
          vector<int> reduced;
          for (size_t j=0; j < working.size(); j++) {
            if (i != j) {
              reduced.push_back(working[j]);
            }
          }
          // marks that both working and -working_i are now unnecessary
          clauses[working] = false;
          working[i] = -working[i];
          clauses[working] = false;
          working[i] = -working[i];
          // Loop to see if an even smaller clause can be made
          unprocessed.push_back(reduced);
        }
        working[i] = -working[i];
      }
    }
  }
  vector<vector<int>> final_clauses;
  size_t final_variables = 0;
  for (const auto pair : clauses) {
    if (not pair.second) {
      continue;
    }
    final_clauses.push_back(pair.first);
    for (const auto v :pair.first) {
      auto variable = static_cast<size_t>(abs(v));
      if (final_variables < variable) {
        final_variables = variable;
      }
    }
  }

  std::ofstream out(filename);
  out << "c Post processed instance" << endl;
  out << "p cnf " << final_variables << " " << final_clauses.size() << endl;
  for (const auto clause : final_clauses) {
    for (const auto v : clause) {
      out << v << " ";
    }
    out << 0 << endl;
  }
}

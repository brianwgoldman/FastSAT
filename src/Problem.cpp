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

vector<char> number_to_row(size_t number, const size_t number_of_variables) {
  // Add a row to the table
  vector<char> row(number_of_variables);
  for (size_t i=0; i < number_of_variables; i++) {
    // Finds the bit value of "position" at i
    row[i] = ((number >> i) & 1);
  }
  return row;
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
  out << " Rows: " << total_rows << std::endl;
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
  dnfs.insert(dnf);
  std::weak_ptr<DNF> weak_dnf = dnf;
  for (const auto v : dnf->get_variables()) {
    variable_to_dnfs[v].insert(weak_dnf);
  }
  requires_knowledge_propagate.insert(weak_dnf);
  requires_assume_and_learn.insert(weak_dnf);
}

void Problem::remove_dnf(std::weak_ptr<DNF>& weak_dnf) {
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
  /*
  for (const auto v : update_required) {
    requires_knowledge_propagate.insert(variable_to_dnfs[v].begin(), variable_to_dnfs[v].end());
  }
  */
  clean_up_bins(update_required);
  // propagate the new knowledge
  knowledge_propagate(global_knowledge, true);
}


std::shared_ptr<DNF> simple_convert(vector<unordered_map<size_t, bool>>& rows) {
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

void Problem::equal_variable_assuming() {
  unordered_map<size_t, size_t> variable_tests;
  size_t loops = 0;
  while (not requires_assume_and_learn.empty()) {
    loops++;
    if (loops > 100) {
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
    //realized_dnf = resolve_overlaps(weak).lock();
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

void Problem::merge_small_rows(const size_t limit) {
  vector<weak_dnf_set> bins(limit);
  // Put every dnf into bins based on its number of rows
  for (const auto dnf : dnfs) {
    if (dnf->get_table().size() < limit) {
      bins[dnf->get_table().size()].insert(dnf);
    }
  }
  bool found;
  size_t shrink=0, total=0, tested=0, no_partner=0;
  do {
    found = false;
    std::weak_ptr<DNF> weak_dnf;
    size_t left_off;
    for (size_t i=0; i < limit; i++) {
      if (not bins[i].empty()) {
        weak_dnf = *bins[i].begin();
        bins[i].erase(weak_dnf);
        left_off = 0;
        found = true;
        break;
      }
    }
    if (not found) {
      break;
    }
    // Find a good partner for this guy
    auto realized_dnf = weak_dnf.lock();
    if(not realized_dnf) {
      continue;
    }
    found = false;
    std::weak_ptr<DNF> weak_final_partner;
    for (size_t i=left_off; i < limit; i++) {
      if (not bins[i].empty()) {
        weak_final_partner = *bins[i].begin();
        bins[i].erase(weak_final_partner);
        if (weak_final_partner.lock()) {
          found = true;
          break;
        }
      }
    }
    if (not found) {
      break;
    }
    auto final_result = std::make_shared<DNF>(DNF::merge(*realized_dnf, *weak_final_partner.lock()));
    size_t smallest = final_result->get_table().size();
    /*
    weak_dnf_set partners;
    // Find the most populated varibale bin this function overlaps
    size_t best_variable = realized_dnf->get_variables()[0];
    for (const auto v : realized_dnf->get_variables()) {
      //partners.insert(variable_to_dnfs[v].begin(), variable_to_dnfs[v].end());
      if (variable_to_dnfs[best_variable].size() < variable_to_dnfs[v].size()) {
        best_variable = v;
      }
    }
    partners = variable_to_dnfs[best_variable];
    // Don't include yourself
    partners.erase(weak_dnf);
    std::weak_ptr<DNF> weak_final_partner;
    std::shared_ptr<DNF> final_result;
    //*
    size_t smallest = -1;
    for (const auto weak_partner : partners) {
      auto realized_partner = weak_partner.lock();
      assert(realized_partner);
      if (realized_partner->get_table().size() < smallest) {
        smallest = realized_partner->get_table().size();
        weak_final_partner = weak_partner;
      }
    }
    final_result = std::make_shared<DNF>(DNF::merge(*realized_dnf, *weak_final_partner.lock()));
    smallest = final_result->get_table().size();
    */
    /*/
    size_t smallest = -1;
    bool shrinking = false;
    for (const auto weak_partner : partners) {
      auto realized_partner = weak_partner.lock();
      //assert(realized_partner);
      if (realized_partner) {
        tested++;
        auto result = std::make_shared<DNF>(DNF::merge(*realized_dnf, *realized_partner));
        auto learned = result->create_knowledge();
        if (not learned.empty()) {
          cout << "Learned from merge" << endl;
          learned.print();
          add_knowledge(learned);
          result->apply_knowledge(global_knowledge);
        }
        if (result->get_table().size() < smallest) {
          weak_final_partner = realized_partner;
          smallest = result->get_table().size();
          final_result = result;
        }
      } else {
        cout << "Missing partner!!" << endl;
      }
    }
    //*/
    if (not weak_final_partner.expired()) {
      total++;
      auto realized_partner = weak_final_partner.lock();
      assert(realized_partner);
      auto partner_rows = realized_partner->get_table().size();
      if (partner_rows < limit) {
        bins[partner_rows].erase(weak_final_partner);
      }
      cout << "Merged: " << realized_dnf->get_variables().size() << "x" << realized_dnf->get_table().size()
           << " + " << realized_partner->get_variables().size() << "x" << realized_partner->get_table().size()
           << " = " << final_result->get_variables().size() << "x" << final_result->get_table().size() << endl;
      cout << "shrink: " << shrink << " / " << total << " tested: " << tested << " no partner: " << no_partner << endl;
      //realized_dnf->print();
      //realized_partner->print();
      //final_result->print();
      // Remove the merged things from the problem
      remove_dnf(weak_dnf);
      remove_dnf(weak_final_partner);
      // And the result
      add_dnf(final_result);
      //*
      if (true or final_result->get_table().size() < limit) {
        final_result = assume_and_learn(final_result);
        auto learned = final_result->create_knowledge();
        if (not learned.empty()) {
          cout << "Learned from the assume-and-learn" << endl;
          learned.print();
          add_knowledge(learned);
        }
        std::weak_ptr<DNF> weak = final_result;
        final_result = resolve_overlaps(weak).lock();
        smallest = final_result->get_table().size();
      }
      print_short();
      //*/
      if (smallest < limit) {
        bins[smallest].insert(final_result);
      }
    } else {
      no_partner++;
    }
  } while (found);
}

std::shared_ptr<DNF> Problem::fill_in_stars(std::shared_ptr<DNF> realized_dnf) {
  cout << "Filling in with " << realized_dnf->get_table().size() << " rows" << endl;
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
  // Find the rows that have either for that column
  auto new_rows = realized_dnf->convert_to_map();
  bool changed = false;
  for (size_t r=0; r < new_rows.size(); r++) {
    if (new_rows[r].count(variable) == 0) {
      // This row doesn't have a value for this variable
      Knowledge assumption;
      assumption.assigned = new_rows[r];
      assumption.add(variable, missing_value);
      propagate_assumption(assumption);

      if (not assumption.is_unsat) {
        cout << "Broke Streak" << endl;
        // Add the row back in (and its consequences) only if it didn't lead to a contradiction
        new_rows.push_back(assumption.assigned);
        // Found a row that breaks the uniformity, so stop
        changed=true;
        break;
      } else {
        cout << "Extended streak" << endl;
        new_rows[r][variable] = not missing_value;
        changed = true;
      }
    }
  }
  if (changed) {
    realized_dnf = std::make_shared<DNF>(new_rows);
  }
  cout << "End of fill in stars" << endl;
  return fill_in_stars(realized_dnf);
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
    cout << "After assumption assignments: " << assumption.assigned.size() << " " << assumption.is_unsat << endl;
    if (not assumption.is_unsat) {
      // Add the row back in (and its consequences) only if it didn't lead to a contradiction
      new_rows.push_back(assumption.assigned);

    }
  }
  auto new_dnf = simple_convert(new_rows);
  //auto new_dnf = std::make_shared<DNF>(new_rows);
  cout << "After " << new_dnf->get_variables().size() << "x" << new_dnf->get_table().size() << endl;
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
    cout << "After " << new_dnf->get_variables().size() << "x" << new_dnf->get_table().size() << endl;
    new_dnf->create_knowledge().print();
    new_dnf = fill_in_stars(new_dnf);
    cout << "Third " << new_dnf->get_variables().size() << "x" << new_dnf->get_table().size() << endl;
    new_dnf->create_knowledge().print();
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

std::weak_ptr<DNF> Problem::merge(std::weak_ptr<DNF>& weak_a, std::weak_ptr<DNF>& weak_b) {
  auto realized_a = weak_a.lock();
  auto realized_b = weak_b.lock();
  assert(realized_a and realized_b);
  auto realized_new = std::make_shared<DNF>(DNF::merge(*realized_a, *realized_b));
  cout << "Merged: " << realized_a->get_table().size()
       << "+" << realized_b->get_table().size()
       << "=" << realized_new->get_table().size() << endl;
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

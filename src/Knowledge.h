// Stores everything concrete that has been learned so far.
// Specifically knows all assignments (e.g. x=0) and 2-Consistencies (e.g. x!=y)
// as well as if a contradiction has been found (is_unsat).
#ifndef KNOWLEDGE_H_
#define KNOWLEDGE_H_
#include <unordered_map>
#include <vector>
using std::vector;
#include <cassert>
#include <iostream>
#include <unordered_set>
using std::unordered_set;

struct TwoConsistency {
  size_t from, to;
  bool negated;
  TwoConsistency(size_t f=0, size_t t=0, bool n=false) : from(f), to(t), negated(n) {
    if (to > from) {
      // Ensures that all 2-Consistencies point in the same direction
      std::swap(to, from);
    }
  }
  void print(std::ostream& out=std::cout) const;
};

// TODO Make some of these things private to better track modifications
class Knowledge {
 public:
  bool is_sat = false;
  bool is_unsat = false;
  std::unordered_map<size_t, bool> assigned;
  std::unordered_map<size_t, TwoConsistency> rewrites;

  // These functions add knowledge and return all variables affected by that new knowledge
  unordered_set<size_t> add(const size_t variable, const bool value);
  unordered_set<size_t> add(const TwoConsistency& rewrite);
  unordered_set<size_t> add(const Knowledge& knowledge);
  bool empty() const {
    return (not is_sat) and (not is_unsat) and assigned.empty() and rewrites.empty();
  }
  void print(std::ostream& out=std::cout) const;
 private:
  // Used to quickly update rewrites when new knowledge is added
  std::unordered_map<size_t, std::vector<size_t>> sources;
};


// TODO Put this somewhere better
#include <algorithm>
template <class T, class U>
void print_map(const std::unordered_map<T, U> & m, std::ostream& out) {
  if (m.empty()) {
    out << "(Empty)" << std::endl;
    return;
  }
  std::vector<T> keys;
  for (const auto pair : m) {
    keys.push_back(pair.first);
  }
  std::sort(keys.begin(), keys.end());
  for (const auto key : keys) {
    out << key << "=" << m.find(key)->second << " ";
  }
  out << std::endl;
}

#endif /* KNOWLEDGE_H_ */

/*
 * Knowledge.h
 *
 *  Created on: Apr 4, 2016
 *      Author: goldman
 */

#ifndef KNOWLEDGE_H_
#define KNOWLEDGE_H_
#include <unordered_map>
#include <vector>
#include <cassert>
#include <iostream>

struct TwoConsistency {
  size_t from, to;
  bool negated;
  TwoConsistency(size_t f=0, size_t t=0, bool n=false) : from(f), to(t), negated(n) {
    if (to > from) {
      std::swap(to, from);
    }
  }
  void print(std::ostream& out=std::cout) const;
};

class Knowledge {
 public:
  bool is_sat = false;
  bool is_unsat = false;
  std::unordered_map<size_t, bool> assigned;
  std::unordered_map<size_t, TwoConsistency> rewrites;
  // Used to quickly update rewrites when new knowledge is added
  std::unordered_map<size_t, std::vector<size_t>> sources;
  void add(const size_t variable, const bool value);
  void add(const TwoConsistency& rewrite);
  void add(const Knowledge& knowledge);
  bool empty() const {
    return (not is_sat) and (not is_unsat) and assigned.empty() and rewrites.empty();
  }
  void print(std::ostream& out=std::cout) const;
};


// TODO Put this somewhere better
#include <algorithm>
template <class T, class U>
void print_map(const std::unordered_map<T, U> & m, std::ostream& out) {
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

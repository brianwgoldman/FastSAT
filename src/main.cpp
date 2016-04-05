// Brian Goldman

#include <iostream>
using namespace std;
#include "Problem.h"

int main(int argc, char * argv[]) {
  if (argc < 2) {
    cout << "Need more arguments" << endl;
    return 1;
  }
  Problem problem;
  problem.load(argv[1]);
  //problem.print(std::cout);
  Knowledge global;
  bool new_stuff = true;
  while (new_stuff) {
    new_stuff = false;
    for (const auto & dnf : problem.dnfs) {
      auto knowledge = dnf->create_knowledge();
      if (not knowledge.empty()) {
        cout << "\t\tLearned Something!" << endl;
        dnf->print();
        knowledge.print();
        global.add(knowledge);
        cout << "New Global" << endl;
        global.print();
        new_stuff = true;
      }
    }
    for (auto & dnf : problem.dnfs) {
      DNF backup = *dnf;
      dnf->apply_knowledge(global);
      if (backup.table != dnf->table) {
        cout << "Change Made" << endl;
        global.print();
        backup.print();
        dnf->print();
      }
    }
  }
  return 0;
}

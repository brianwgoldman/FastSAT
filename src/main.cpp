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
  problem.knowledge_propagate();
  problem.global_knowledge.print();

  problem.assume_and_learn();
  cout << "Done!" << endl;
  problem.global_knowledge.print();
  cout << "Try that again" << endl;
  problem.assume_and_learn();
  problem.global_knowledge.print();
  problem.knowledge_propagate();
  problem.print();
  return 0;
}

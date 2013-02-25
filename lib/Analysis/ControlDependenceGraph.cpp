//===- llvm/Analysis/ControlDependenceGraph.cpp -----------------*- C++ -*-===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file defines the ControlDependenceGraph class, which allows fast and 
// efficient control dependence queries. It is based on Ferrante et al's "The 
// Program Dependence Graph and Its Use in Optimization."
//
//===----------------------------------------------------------------------===//

#include "Analysis/ControlDependenceGraph.h"

#include "llvm/Function.h"
#include "llvm/Analysis/DOTGraphTraitsPass.h"
#include "llvm/Support/CFG.h"

#include <deque>
#include <set>

using namespace llvm;

namespace llvm {

void ControlDependenceNode::setTrue(ControlDependenceNode *Child) {
  if (binaryControl) {
    assert(Children.size() == 2);
    Children[0] = Child;
  } else {
    assert(Children.size() == 0);
    Children[0] = Child;
    Children[1] = NULL;
  }
}

void ControlDependenceNode::setFalse(ControlDependenceNode *Child) {
  if (binaryControl) {
    assert(Children.size() == 2);
    Children[1] = Child;
  } else {
    assert(Children.size() == 0);
    Children[0] = NULL;
    Children[1] = Child;
  }
}

void ControlDependenceNode::addOther(ControlDependenceNode *Child) {
  assert(!binaryControl);
  Children.push_back(Child);
}

void ControlDependenceNode::addParent(ControlDependenceNode *Parent) {
  const_iterator I = std::find(Parent->begin(), Parent->end(), this);
  assert(I != Parent->end() && "Must be a child before adding a parent!");
  Parents.push_back(Parent);
}

char ControlDependenceGraph::ID = 0;

bool ControlDependenceGraph::runOnFunction(Function &F) {
  const PostDominatorTree &pdt = getAnalysis<PostDominatorTree>();

  for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
    ControlDependenceNode *bn = new ControlDependenceNode(BB);
    nodes.push_back(bn);
    bbMap[BB] = bn;
  }

  for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
    BasicBlock *cur = BB;
    ControlDependenceNode *A = bbMap[cur];

    for (succ_iterator succ = succ_begin(cur), end = succ_end(cur); succ != end; ++succ) {
      if (!pdt.dominates(*succ,cur)) {
	DomTreeNode *N = pdt.getNode(*succ);
	DomTreeNode *L = pdt.getNode(cur)->getIDom();
	for (; N != L; N = N->getIDom()) {
	  ControlDependenceNode *B = bbMap[N->getBlock()];
	  A->addOther(B);
	  B->addParent(A);
	}
      }
    }
  }

  root = bbMap[&F.getEntryBlock()];

  return false;
}

bool ControlDependenceGraph::controls(BasicBlock *A, BasicBlock *B) const {
  const ControlDependenceNode *n = getNode(B);
  assert(n && "Basic block not in control dependence graph!");
  while (n->getNumParents() == 1) {
    n = *n->parent_begin();
    if (n->getBlock() == A)
      return true;
  }
  return false;
}

bool ControlDependenceGraph::influences(BasicBlock *A, BasicBlock *B) const {
  const ControlDependenceNode *n = getNode(B);
  assert(n && "Basic block not in control dependence graph!");

  std::deque<ControlDependenceNode *> worklist;
  worklist.insert(worklist.end(), n->parent_begin(), n->parent_end());

  while (!worklist.empty()) {
    n = worklist.front();
    worklist.pop_front();
    if (n->getBlock() == A) return true;
    worklist.insert(worklist.end(), n->parent_begin(), n->parent_end());
  }

  return false;
}

} // namespace llvm

namespace {

struct ControlDependenceViewer
  : public DOTGraphTraitsViewer<ControlDependenceGraph, false> {
  static char ID;
  ControlDependenceViewer() : 
    DOTGraphTraitsViewer<ControlDependenceGraph, false>("control-deps", ID) {}
};

struct ControlDependencePrinter
  : public DOTGraphTraitsPrinter<ControlDependenceGraph, false> {
  static char ID;
  ControlDependencePrinter() :
    DOTGraphTraitsPrinter<ControlDependenceGraph, false>("control-deps", ID) {}
};

} // end anonymous namespace

char ControlDependenceViewer::ID = 0;
static RegisterPass<ControlDependenceViewer> Viewer("view-control-deps",
						    "View the control dependency graph",
						    true, true);

char ControlDependencePrinter::ID = 0;
static RegisterPass<ControlDependencePrinter> Printer("print-control-deps",
						      "Print the control dependency graph as a 'dot' file",
						      true, true);

static RegisterPass<ControlDependenceGraph> Graph("control-deps",
						  "Compute control dependency graphs",
						  true, true);

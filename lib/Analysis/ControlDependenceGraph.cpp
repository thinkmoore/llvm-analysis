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

char ControlDependenceGraph::ID = 0;

void ControlDependenceNode::setTrue(ControlDependenceNode *Child) {
  if (binaryControl) {
    assert(Children.size() == 2);
    Children[0] = Child;
  } else {
    assert(Children.size() == 0);
    Children.push_back(Child);
    Children.push_back(NULL);
    binaryControl = true;
  }
}

void ControlDependenceNode::setFalse(ControlDependenceNode *Child) {
  if (binaryControl) {
    assert(Children.size() == 2);
    Children[1] = Child;
  } else {
    assert(Children.size() == 0);
    Children.push_back(NULL);
    Children.push_back(Child);
    binaryControl = true;
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

ControlDependenceNode::EdgeType ControlDependenceNode::getEdgeType(const ControlDependenceNode *other) const {
  if (!other || isRegion() || other->isRegion()) return OTHER;

  if (const BranchInst *b = dyn_cast<BranchInst>(TheBB->getTerminator())) {
    if (b->isConditional()) {
      if (b->getSuccessor(0) == other->getBlock()) {
	return TRUE;
      } else {
	assert(b->getSuccessor(1) == other->getBlock());
	return FALSE;
      }
    }
  }
  return OTHER;
}

void ControlDependenceGraph::computeDependencies(Function &F) {
  PostDominatorTree &pdt = getAnalysis<PostDominatorTree>();

  root = new ControlDependenceNode();
  nodes.push_back(root);
  for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
    ControlDependenceNode *bn = new ControlDependenceNode(BB);
    nodes.push_back(bn);
    bbMap[BB] = bn;
  }

  for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
    BasicBlock *A = BB;
    ControlDependenceNode *AN = bbMap[A];

    for (succ_iterator succ = succ_begin(A), end = succ_end(A); succ != end; ++succ) {
      BasicBlock *B = *succ;
      ControlDependenceNode *BN = bbMap[B];
      errs() << "Does " << B->getName() << " post-dominate " << A->getName() << "? ";
      if (A == B || !pdt.dominates(B,A)) {
	errs() << "no\n";
	BasicBlock *L = pdt.findNearestCommonDominator(A,B);
	errs() << "\tleast common dominator is " << L->getName() << "\n";
	ControlDependenceNode::EdgeType type = AN->getEdgeType(BN);
	if (A == L) {
	  switch (type) {
	  case ControlDependenceNode::TRUE:
	    AN->setTrue(AN); break;
	  case ControlDependenceNode::FALSE:
	    AN->setFalse(AN); break;
	  case ControlDependenceNode::OTHER:
	    AN->addOther(AN); break;
	  }
	  AN->addParent(AN);
	}
	for (DomTreeNode *cur = pdt[B]; cur && cur != pdt[L]; cur = cur->getIDom()) {
	  errs() << "\t\tAdding edge from " << A->getName() << " to " << cur->getBlock()->getName() << "\n";
	  ControlDependenceNode *CN = bbMap[cur->getBlock()];
	  switch (type) {
	  case ControlDependenceNode::TRUE:
	    AN->setTrue(CN); break;
	  case ControlDependenceNode::FALSE:
	    AN->setFalse(CN); break;
	  case ControlDependenceNode::OTHER:
	    AN->addOther(CN); break;
	  }
	  CN->addParent(AN);
	}
      } else {
	errs() << "yes\n";
      }
    }
  }

  // ENTRY -> START
  errs() << "Does " << F.getEntryBlock().getName() << " post-dominate ENTRY? no\n";
  errs() << "\tleast common dominator is EXIT\n";
  for (DomTreeNode *cur = pdt[&F.getEntryBlock()]; cur; cur = cur->getIDom()) {
    errs() << "\t\tAdding edge from " << F.getEntryBlock().getName() << " to " << cur->getBlock()->getName() << "\n";
    ControlDependenceNode *CN = bbMap[cur->getBlock()];
    root->addOther(CN); CN->addParent(root);
  }
}

void ControlDependenceGraph::insertRegions() {

}

bool ControlDependenceGraph::runOnFunction(Function &F) {
  computeDependencies(F);
  insertRegions();
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

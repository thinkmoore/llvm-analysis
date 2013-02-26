//===- Analysis/ControlDependenceGraph.cpp ----------------------*- C++ -*-===//
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

void ControlDependenceNode::addTrue(ControlDependenceNode *Child) {
  TrueChildren.push_back(Child);
}

void ControlDependenceNode::addFalse(ControlDependenceNode *Child) {
  FalseChildren.push_back(Child);
}

void ControlDependenceNode::addOther(ControlDependenceNode *Child) {
  OtherChildren.push_back(Child);
}

void ControlDependenceNode::addParent(ControlDependenceNode *Parent) {
  assert(std::find(Parent->begin(), Parent->end(), this) != Parent->end()
  	 && "Must be a child before adding the parent!");
  Parents.push_back(Parent);
}

ControlDependenceNode::EdgeType
ControlDependenceGraph::getEdgeType(const BasicBlock *A, const BasicBlock *B) {
  if (const BranchInst *b = dyn_cast<BranchInst>(A->getTerminator())) {
    if (b->isConditional()) {
      if (b->getSuccessor(0) == B) {
	return ControlDependenceNode::TRUE;
      } else if (b->getSuccessor(1) == B) {
	return ControlDependenceNode::FALSE;
      } else {
	assert(false && "Asking for edge type between unconnected basic blocks!");
      }
    }
  }
  return ControlDependenceNode::OTHER;
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
      errs() << "Does " << B->getName() << " post-dominate " << A->getName() << "? ";
      if (A == B || !pdt.dominates(B,A)) {
	errs() << "no\n";
	BasicBlock *L = pdt.findNearestCommonDominator(A,B);
	errs() << "\tleast common dominator is " << L->getName() << "\n";
	ControlDependenceNode::EdgeType type = ControlDependenceGraph::getEdgeType(A,B);
	if (A == L) {
	  errs() << "\t\tA == L, Adding ";
	  switch (type) {
	  case ControlDependenceNode::TRUE:
	    errs() << "TRUE";
	    AN->addTrue(AN); break;
	  case ControlDependenceNode::FALSE:
	    errs() << "FALSE";
	    AN->addFalse(AN); break;
	  case ControlDependenceNode::OTHER:
	    errs() << "OTHER";
	    AN->addOther(AN); break;
	  }
	  AN->addParent(AN);
	  errs() << " self edge\n";
	}
	for (DomTreeNode *cur = pdt[B]; cur && cur != pdt[L]; cur = cur->getIDom()) {
	  errs() << "\t\tAdding ";
	  ControlDependenceNode *CN = bbMap[cur->getBlock()];
	  switch (type) {
	  case ControlDependenceNode::TRUE:
	    errs() << "TRUE";
	    AN->addTrue(CN); break;
	  case ControlDependenceNode::FALSE:
	    errs() << "FALSE";
	    AN->addFalse(CN); break;
	  case ControlDependenceNode::OTHER:
	    errs() << "OTHER";
	    AN->addOther(CN); break;
	  }
	  CN->addParent(AN);
	  errs() << " edge from " << A->getName() << " to " << cur->getBlock()->getName() << "\n";
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
    errs() << "\t\tAdding edge from ENTRY to " << cur->getBlock()->getName() << "\n";
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

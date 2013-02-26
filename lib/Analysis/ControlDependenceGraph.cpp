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
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/Support/CFG.h"

#include <deque>
#include <set>

using namespace llvm;

namespace llvm {

char ControlDependenceGraph::ID = 0;

void ControlDependenceNode::addTrue(ControlDependenceNode *Child) {
  TrueChildren.insert(Child);
}

void ControlDependenceNode::addFalse(ControlDependenceNode *Child) {
  FalseChildren.insert(Child);
}

void ControlDependenceNode::addOther(ControlDependenceNode *Child) {
  OtherChildren.insert(Child);
}

void ControlDependenceNode::addParent(ControlDependenceNode *Parent) {
  assert(std::find(Parent->begin(), Parent->end(), this) != Parent->end()
  	 && "Must be a child before adding the parent!");
  Parents.insert(Parent);
}

void ControlDependenceNode::removeTrue(ControlDependenceNode *Child) {
  node_iterator CN = TrueChildren.find(Child);
  if (CN != TrueChildren.end())
    TrueChildren.erase(CN);
}

void ControlDependenceNode::removeFalse(ControlDependenceNode *Child) {
  node_iterator CN = FalseChildren.find(Child);
  if (CN != FalseChildren.end())
    FalseChildren.erase(CN);
}

void ControlDependenceNode::removeOther(ControlDependenceNode *Child) {
  node_iterator CN = OtherChildren.find(Child);
  if (CN != OtherChildren.end())
    OtherChildren.erase(CN);
}

void ControlDependenceNode::removeParent(ControlDependenceNode *Parent) {
  node_iterator PN = Parents.find(Parent);
  if (PN != Parents.end())
    Parents.erase(PN);
}

const ControlDependenceNode *ControlDependenceNode::enclosingRegion() const {
  if (this->isRegion()) {
    return this;
  } else {
    assert(this->Parents.size() == 1);
    const ControlDependenceNode *region = *this->Parents.begin();
    assert(region->isRegion());
    return region;
  }
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
  nodes.insert(root);
  for (Function::iterator BB = F.begin(), E = F.end(); BB != E; ++BB) {
    ControlDependenceNode *bn = new ControlDependenceNode(BB);
    nodes.insert(bn);
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
  PostDominatorTree &pdt = getAnalysis<PostDominatorTree>();

  typedef po_iterator<PostDominatorTree*> po_pdt_iterator;  
  typedef std::pair<ControlDependenceNode::EdgeType, ControlDependenceNode *> cd_type;
  typedef std::set<cd_type> cd_set_type;
  typedef std::map<cd_set_type, ControlDependenceNode *> cd_map_type;

  cd_map_type cdMap;

  for (po_pdt_iterator DTN = po_pdt_iterator::begin(&pdt), END = po_pdt_iterator::end(&pdt);
       DTN != END; ++DTN) {
    ControlDependenceNode *node = bbMap[DTN->getBlock()];

    cd_set_type cds;
    for (ControlDependenceNode::node_iterator P = node->Parents.begin(), E = node->Parents.end(); P != E; ++P) {
      ControlDependenceNode *parent = *P;
      if (parent->TrueChildren.find(node) != parent->TrueChildren.end())
	cds.insert(std::make_pair(ControlDependenceNode::TRUE, parent));
      if (parent->FalseChildren.find(node) != parent->FalseChildren.end())
	cds.insert(std::make_pair(ControlDependenceNode::FALSE, parent));
      if (parent->OtherChildren.find(node) != parent->OtherChildren.end())
	cds.insert(std::make_pair(ControlDependenceNode::OTHER, parent));
    }

    cd_map_type::iterator CDEntry = cdMap.find(cds);
    ControlDependenceNode *region;
    if (CDEntry == cdMap.end()) {
      region = new ControlDependenceNode();
      nodes.insert(region);
      cdMap.insert(std::make_pair(cds,region));
      for (cd_set_type::iterator CD = cds.begin(), CDEnd = cds.end(); CD != CDEnd; ++CD) {
	switch (CD->first) {
	case ControlDependenceNode::TRUE:
	  CD->second->addTrue(region);
	  break;
	case ControlDependenceNode::FALSE:
	  CD->second->addFalse(region);
	  break;
	case ControlDependenceNode::OTHER:
	  CD->second->addOther(region); 
	  break;
	}
	region->addParent(CD->second);
      }
    } else {
      region = CDEntry->second;
    }
    for (cd_set_type::iterator CD = cds.begin(), CDEnd = cds.end(); CD != CDEnd; ++CD) {
      switch (CD->first) {
      case ControlDependenceNode::TRUE:
	CD->second->removeTrue(node);
	break;
      case ControlDependenceNode::FALSE:
	CD->second->removeFalse(node);
	break;
      case ControlDependenceNode::OTHER:
	CD->second->removeOther(node);
	break;
      }
      region->addOther(node);
      node->addParent(region);
      node->removeParent(CD->second);
    }
  }

  // Make sure that each node has at most one true or false edge
  for (std::set<ControlDependenceNode *>::iterator N = nodes.begin(), E = nodes.end();
       N != E; ++N) {
    ControlDependenceNode *node = *N;
    assert(node);
    if (node->isRegion())
      continue;

    // Fix too many true nodes
    if (node->TrueChildren.size() > 1) {
      ControlDependenceNode *region = new ControlDependenceNode();
      nodes.insert(region);
      for (ControlDependenceNode::node_iterator C = node->true_begin(), CE = node->true_end();
	   C != CE; ++C) {
	ControlDependenceNode *child = *C;
	assert(node);
	assert(child);
	assert(region);
	region->addOther(child);
	child->addParent(region);
	child->removeParent(node);
	node->removeTrue(child);
      }
      node->addTrue(region);
    }

    // Fix too many false nodes
    if (node->FalseChildren.size() > 1) {
      ControlDependenceNode *region = new ControlDependenceNode();
      nodes.insert(region);
      for (ControlDependenceNode::node_iterator C = node->false_begin(), CE = node->false_end();
	   C != CE; ++C) {
	ControlDependenceNode *child = *C;
	region->addOther(child);
	child->addParent(region);
	child->removeParent(node);
	node->removeFalse(child);
      }
      node->addFalse(region);
    }
  }
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

const ControlDependenceNode *ControlDependenceGraph::enclosingRegion(BasicBlock *BB) const {
  if (const ControlDependenceNode *node = this->getNode(BB)) {
    return node->enclosingRegion();
  } else {
    return NULL;
  }
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

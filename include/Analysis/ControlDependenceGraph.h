//===- llvm/Analysis/ControlDependenceGraph.h -------------------*- C++ -*-===//
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

#ifndef ANALYSIS_CONTROLDEPENDENCEGRAPH_H
#define ANALYSIS_CONTROLDEPENDENCEGRAPH_H

#include "llvm/ADT/DepthFirstIterator.h"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/Analysis/PostDominators.h"
#include "llvm/Pass.h"
#include "llvm/Support/DOTGraphTraits.h"

#include <vector>
#include <map>

namespace llvm {

class BasicBlock;
class ControlDependenceGraph;

class ControlDependenceNode {
public:
  typedef std::vector<ControlDependenceNode *>::iterator iterator;
  typedef std::vector<ControlDependenceNode *>::const_iterator const_iterator;

  iterator begin()             { return Children.begin(); }
  iterator end()               { return Children.end(); }
  const_iterator begin() const { return Children.begin(); }
  const_iterator end()   const { return Children.end(); }

  iterator parent_begin()             { return Parents.begin(); }
  iterator parent_end()               { return Parents.end(); }
  const_iterator parent_begin() const { return Parents.begin(); }
  const_iterator parent_end()   const { return Parents.end(); }

  BasicBlock *getBlock() const { return TheBB; }
  const ControlDependenceNode *getTrue() const {
    assert(!binaryControl || Children.size() >= 2);
    return binaryControl ? Children[0] : NULL;
  }
  ControlDependenceNode *getTrue() {
    assert(!binaryControl || Children.size() >= 2);
    return binaryControl ? Children[0] : NULL;
  }
  const ControlDependenceNode *getFalse() const { 
    assert(!binaryControl || Children.size() >= 2);
    return binaryControl ? Children[1] : NULL;
  }
  ControlDependenceNode *getFalse() {
    assert(!binaryControl || Children.size() >= 2);
    return binaryControl ? Children[1] : NULL;
  }

  size_t getNumParents() const { return Parents.size(); }
  size_t getNumChildren() const { return Children.size(); }
  bool isBinary() const { return binaryControl; }

  void clearAllChildren() { 
    Children.clear();
    binaryControl = false;
  }
  void clearAllParents() { Parents.clear(); }

  void setTrue(ControlDependenceNode *Child);
  void setFalse(ControlDependenceNode *Child);
  void addOther(ControlDependenceNode *Child);
  void addParent(ControlDependenceNode *Parent);

  bool isRegion() const { return TheBB == NULL; }

  ControlDependenceNode() : TheBB(NULL), binaryControl(false) {};
  ControlDependenceNode(BasicBlock *bb) : TheBB(bb), binaryControl(false) {};

private:
  BasicBlock *TheBB;
  bool binaryControl;
  std::vector<ControlDependenceNode *> Parents;
  std::vector<ControlDependenceNode *> Children;
};

template <> struct GraphTraits<ControlDependenceNode *> {
  typedef ControlDependenceNode NodeType;
  typedef NodeType::iterator ChildIteratorType;

  static NodeType *getEntryNode(NodeType *N) { return N; }

  static inline ChildIteratorType child_begin(NodeType *N) {
    return N->begin();
  }
  static inline ChildIteratorType child_end(NodeType *N) {
    return N->end();
  }

  typedef df_iterator<ControlDependenceNode *> nodes_iterator;

  static nodes_iterator nodes_begin(ControlDependenceNode *N) {
    return df_begin(getEntryNode(N));
  }
  static nodes_iterator nodes_end(ControlDependenceNode *N) {
    return df_end(getEntryNode(N));
  }
};
  
class ControlDependenceGraph : public FunctionPass {
public:
  static char ID; // Pass identification, replacement for typeid

  ControlDependenceGraph() : FunctionPass(ID) {}
  ~ControlDependenceGraph() {
    for (std::vector<ControlDependenceNode *>::iterator n = nodes.begin(), e = nodes.end();
	 n != e; ++n)
      delete *n;
  }

  virtual bool runOnFunction(Function &F);

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<PostDominatorTree>();
    AU.setPreservesAll();
  }

  ControlDependenceNode *getRoot()             { return root; }
  const ControlDependenceNode *getRoot() const { return root; }
  ControlDependenceNode *operator[](BasicBlock *BB)             { return getNode(BB); }
  const ControlDependenceNode *operator[](BasicBlock *BB) const { return getNode(BB); }
  ControlDependenceNode *getNode(BasicBlock *BB) { 
    return bbMap[BB];
  }
  const ControlDependenceNode *getNode(BasicBlock *BB) const {
    return (bbMap.find(BB) != bbMap.end()) ? bbMap.find(BB)->second : NULL;
  }
  bool controls(BasicBlock *A, BasicBlock *B) const;
  bool influences(BasicBlock *A, BasicBlock *B) const;

private:
  ControlDependenceNode *root;
  std::vector<ControlDependenceNode *> nodes;
  std::map<BasicBlock *,ControlDependenceNode *> bbMap;
};

template <> struct GraphTraits<ControlDependenceGraph *>
  : public GraphTraits<ControlDependenceNode *> {
  static NodeType *getEntryNode(ControlDependenceGraph *CD) {
    return CD->getRoot();
  }

  static nodes_iterator nodes_begin(ControlDependenceGraph *CD) {
    if (getEntryNode(CD))
      return df_begin(getEntryNode(CD));
    else
      return df_end(getEntryNode(CD));
  }

  static nodes_iterator nodes_end(ControlDependenceGraph *CD) {
    return df_end(getEntryNode(CD));
  }
};

template <> struct DOTGraphTraits<const ControlDependenceGraph *>
  : public DefaultDOTGraphTraits {
  DOTGraphTraits(bool isSimple = false) : DefaultDOTGraphTraits(isSimple) {}

  static std::string getGraphName(ControlDependenceGraph *Graph) {
    return "Control dependence graph";
  }

  std::string getNodeLabel(const ControlDependenceNode *Node, const ControlDependenceGraph *Graph) {
    if (Node->isRegion()) {
      return "REGION";
    } else {
      return Node->getBlock()->hasName() ? Node->getBlock()->getName() : "ENTRY";
    }
  }
};

} // namespace llvm

#endif // ANALYSIS_CONTROLDEPENDENCEGRAPH_H

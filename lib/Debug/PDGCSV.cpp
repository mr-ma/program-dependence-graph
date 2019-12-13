#include "SVF/MSSA/SVFG.h"
#include "SVF/MSSA/SVFGBuilder.h"
#include "SVF/MemoryModel/PointerAnalysis.h"
#include "SVF/Util/SVFModule.h"
#include "SVF/WPA/Andersen.h"
#include "PDG/Passes/PDGBuildPasses.h"
#include "PDG/PDG.h"
#include "PDG/PDGNode.h"
#include "PDG/PDGLLVMNode.h"
#include "PDG/PDGEdge.h"
#include "PDG/FunctionPDG.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/PassRegistry.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/GraphWriter.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <fstream>
#include <filesystem>
#include <iostream>
#include <functional>
#include <sstream>
#include <unordered_set>
#include <regex>

using namespace llvm;
namespace fs = std::filesystem;
static llvm::cl::opt<std::string>
    BlocksFile("blocks", cl::Hidden,
               cl::desc("File path to blocks features CSV file "));

static llvm::cl::opt<std::string>
    RelationsFile("relations", cl::Hidden,
                  cl::desc("File path to the block relations CSV file "));

static cl::opt<bool> Append("append", cl::Hidden,
                            cl::desc("Append to the specified file"));

class PDGCSV : public llvm::ModulePass {
public:
  static char ID;
  PDGCSV() : llvm::ModulePass(ID) {}
  bool hasIncomingEdges(PAGNode *pagNode) {
    // Addr, Copy, Store, Load, Call, Ret, NormalGep, VariantGep, ThreadFork,
    // ThreadJoin
    if (pagNode->hasIncomingEdges(PAGEdge::Addr) ||
        pagNode->hasIncomingEdges(PAGEdge::Copy) ||
        pagNode->hasIncomingEdges(PAGEdge::Store) ||
        pagNode->hasIncomingEdges(PAGEdge::Load) ||
        pagNode->hasIncomingEdges(PAGEdge::Call) ||
        pagNode->hasIncomingEdges(PAGEdge::Ret) ||
        pagNode->hasIncomingEdges(PAGEdge::NormalGep) ||
        pagNode->hasIncomingEdges(PAGEdge::VariantGep) ||
        pagNode->hasIncomingEdges(PAGEdge::ThreadFork) ||
        pagNode->hasIncomingEdges(PAGEdge::ThreadJoin)) {
      return true;
    }
    return false;
  }

  bool hasOutgoingEdges(PAGNode *pagNode) {
    // Addr, Copy, Store, Load, Call, Ret, NormalGep, VariantGep, ThreadFork,
    // ThreadJoin
    if (pagNode->hasOutgoingEdges(PAGEdge::Addr) ||
        pagNode->hasOutgoingEdges(PAGEdge::Copy) ||
        pagNode->hasOutgoingEdges(PAGEdge::Store) ||
        pagNode->hasOutgoingEdges(PAGEdge::Load) ||
        pagNode->hasOutgoingEdges(PAGEdge::Call) ||
        pagNode->hasOutgoingEdges(PAGEdge::Ret) ||
        pagNode->hasOutgoingEdges(PAGEdge::NormalGep) ||
        pagNode->hasOutgoingEdges(PAGEdge::VariantGep) ||
        pagNode->hasOutgoingEdges(PAGEdge::ThreadFork) ||
        pagNode->hasOutgoingEdges(PAGEdge::ThreadJoin)) {
      return true;
    }
    return false;
  }
  void getAnalysisUsage(llvm::AnalysisUsage& AU) const{
     AU.addRequired<pdg::SVFGPDGBuilder>();
     AU.setPreservesAll();
  }
  bool runOnModule(llvm::Module &M) override {
    SVFModule svfM(M);
    AndersenWaveDiff *ander = new AndersenWaveDiff();
    ander->disablePrintStat();
    ander->analyze(svfM);
    SVFGBuilder memSSA(true);
    SVFG *svfg = memSSA.buildSVFG((BVDataPTAImpl *)ander);

    auto pdgp = getAnalysis<pdg::SVFGPDGBuilder>().getPDG();
    if (RelationsFile.empty() || BlocksFile.empty()) {
      llvm::errs()
          << "-relations and -blocks must be supplied (path to CSV files)";
      exit(1);
    }
    // std::ofstream blockfile, blockrelfile, instructionfile;
    FILE *blockfile, *blockrelfile;
    std::string fileMode = Append ? "a" : "w";
    blockrelfile = fopen(RelationsFile.c_str(), fileMode.c_str());
    blockfile = fopen(BlocksFile.c_str(), fileMode.c_str());
    auto *pag = svfg->getPAG();
    std::vector<std::size_t> blockIds;
    std::vector<tuple<size_t, std::vector<int>, std::string, std::string>>
        blockFeatures;
    std::vector<std::pair<std::size_t, std::size_t>> blockSCCRelationIds,
        blockCFGRelationIds;
    std::vector<std::tuple<std::size_t, std::size_t,std::string>> blockSVFRelationIds;
    std::vector<size_t> soloBlocks;
    for (auto &F : M) {
      if (F.isDeclaration()) {
        continue;
      }
      llvm::dbgs() << "Function   " << F.getName() << "\n";
      auto fpdg = pdgp->getFunctionPDG(&F);
      for (auto &B : F) {
        featureVector.clear();
        auto blockId = getUniqueBlockName(&B, &F);
        blockIds.push_back(blockId);

        ///--------------Handle CFG Relations -------------
	bool hasSuccBlocks = false;
	//llvm::dbgs()<<"block:"<<blockId<<" successors:\n";
	for(BasicBlock *succBB: successors(&B)){
	  size_t succBlockId = getUniqueBlockName(succBB, succBB->getParent());
	  //llvm::dbgs()<<succBlockId<<", ";
	  blockCFGRelationIds.push_back(std::make_pair(blockId,succBlockId));
	  hasSuccBlocks = true;
	}
	//llvm::dbgs()<<"\n";
	//if(!hasSuccBlocks){
	 // llvm::dbgs()<<"No successor:"<<blockId<<"\n";
	 // B.print(dbgs());
	 // dbgs()<<"num succ:"<<B.getTerminator()->getNumSuccessors()<<"\n";
	//}
        //---------------End of CFG reltions --------------
	
        //llvm::dbgs() << "BB: " << blockId << "\n";
        std::vector<std::tuple<std::size_t, std::size_t,std::string>> BBOutBBs;
        std::string BBLabel = "none";
        // getCleanBBContent(&B);
        std::string blockContent = "";
	bool hasSVF = false;
        for (auto &I : B) {
          llvm::raw_string_ostream rso(blockContent);
          I.print(rso);
          blockContent += "|.|";
          //llvm::dbgs() << "Instr: " << I << "\n";
          process(svfg, &I);
          
          auto instOutBBs = getOutEdgeBB(fpdg, &I, &F, blockId);
          if (instOutBBs.size() > 0) {
            BBOutBBs.insert(BBOutBBs.end(), instOutBBs.begin(),
                            instOutBBs.end());
	    hasSVF = true;
          } 
	  std::sort(BBOutBBs.begin(),BBOutBBs.end());
	  BBOutBBs.erase(std::unique(BBOutBBs.begin(),BBOutBBs.end()),BBOutBBs.end());
          blockSVFRelationIds.insert(blockSVFRelationIds.end(),
                                     BBOutBBs.begin(), BBOutBBs.end());
          //llvm::dbgs() << "---------------\n";
          auto instLabel = getInstLabel(I);
          if (instLabel.compare("none") != 0)
            BBLabel = instLabel;
        }
        if(!hasSuccBlocks && !hasSVF) {
          soloBlocks.push_back(blockId);
	  if(BBLabel.compare("none")!=0){
	    llvm::errs()<<"Labled block with no relations found!\n";
	    //B.print(llvm::errs());
	    //exit(1);
	   }  
	}
	std::replace(blockContent.begin(),blockContent.end(),';',' ');
        blockFeatures.push_back(std::make_tuple(blockId, featureVector, BBLabel, blockContent));
        // dumpBBFeatures(blockfile, blockId, featureVector,
        // BBLabel,blockContent); blockfile.flush();
      }

      unsigned sccNum = 0;
      BasicBlock *previousBlock = nullptr;
      // errs() << "SCCs for Function " << F.getName() << " in PostOrder:";
      for (scc_iterator<Function *> SCCI = scc_begin(&F); !SCCI.isAtEnd();
           ++SCCI) {
        const std::vector<BasicBlock *> &nextSCC = *SCCI;
        ++sccNum;
        std::size_t previous = -1;
	//dbgs()<<"SCC group-----\n";
        for (std::vector<BasicBlock *>::const_iterator I = nextSCC.begin(),
                                                       E = nextSCC.end();
             I != E; ++I) {
          size_t current = getUniqueBlockName((*I), &F);
	  //dbgs()<<current<<", ";
          bool relationAdded = false;
          if (previous != -1) {
            blockSCCRelationIds.push_back(make_pair(current, previous));
            relationAdded = true;
          } else if (previousBlock != nullptr) {
            // first bb should be connected to the previous function by scc
            size_t bbIdPreviousFunc =
                getUniqueBlockName(previousBlock, previousBlock->getParent());
            blockSCCRelationIds.push_back(make_pair(bbIdPreviousFunc, current));
            relationAdded = true;
          }
          // now that there is scc relation, the block is not relationless
          // thus we remove it from soloBlocks vector
          if (relationAdded && std::find(soloBlocks.begin(), soloBlocks.end(),
                                         current) != soloBlocks.end()) {
            soloBlocks.erase(
                std::remove(soloBlocks.begin(), soloBlocks.end(), current),
                soloBlocks.end());
          }
          previous = current;
        }
	//dbgs()<<"--------\n";
        previousBlock = (*nextSCC.begin());
      }
    }

    std::sort(blockSCCRelationIds.begin(),blockSCCRelationIds.end());
    blockSCCRelationIds.erase(std::unique(blockSCCRelationIds.begin(),blockSCCRelationIds.end()),blockSCCRelationIds.end());


    /*auto tempIds = blockSVFRelationIds;
    tempIds.insert(tempIds.end(), blockSCCRelationIds.begin(),
                   blockSCCRelationIds.end());
    bool relationErrors, blockErrors = false;
    // Sanity checks
    for (auto &[sBid, dBid] : tempIds) {
      if (std::find(blockIds.begin(), blockIds.end(), sBid) == blockIds.end() ||
          std::find(blockIds.begin(), blockIds.end(), dBid) == blockIds.end()) {
        errs()
            << "ERROR. sid or did blocks were not found in the blocks list\n";
        blockErrors = true;
        exit(1);
      }
    }*/
    //IF block is not in any side of the relations it is a solo block
    vector<size_t> badBlocks;
    for(auto &bid:soloBlocks){
      bool hasSCC = std::find_if(blockSCCRelationIds.begin(), blockSCCRelationIds.end(),
                       [&](std::pair<std::size_t, std::size_t> const &ref) {
                         return ref.second == bid;
                       }) != blockSCCRelationIds.end();
      bool hasCFG = std::find_if(blockCFGRelationIds.begin(), blockCFGRelationIds.end(),
                       [&](std::pair<std::size_t, std::size_t> const &ref) {
                         return ref.second == bid;
                       }) != blockCFGRelationIds.end();
      bool hasSVF = std::find_if(blockSVFRelationIds.begin(), blockSVFRelationIds.end(),
                       [&](std::tuple<std::size_t, std::size_t, std::string> const &ref) {
                         return std::get<1>(ref) == bid;
                       }) != blockSVFRelationIds.end();
      if(!hasSCC && !hasCFG && !hasSVF){
	badBlocks.push_back(bid);
      }

    }
    for (auto &[bid, features, label, content] : blockFeatures) {
      if (std::find(badBlocks.begin(), badBlocks.end(), bid) ==
          badBlocks.end()) {
        dumpBBFeatures(blockfile, bid, features, M.getName().str(),label, content);
      } else {
        errs() << bid << " not in relation with anyone \n";
      }
    }
    /*for (auto &bid : blockIds) {
       if (std::find_if(tempIds.begin(), tempIds.end(),
                       [&](std::pair<std::size_t, std::size_t> const &ref) {
                         return ref.first == bid || ref.second == bid;
                       }) == tempIds.end()) {
        if(std::find(soloBlocks.begin(),soloBlocks.end(),bid)!=soloBlocks.end()){
        errs() << bid << " not in relation with anyone \n";
        // errs() << "\nError. Found blocks with no relations "
        //          "lists!\n";
        // exit(1);
        relationErrors = true;
      }else {
       auto it = std::find_if(blockFeatures.begin(), blockFeatures.end(),
                       [&](std::tuple<std::size_t, vector<int>,std::string,
    std::string> const &ref) { return std::get<0>(ref) == bid;
                       });
       if(it!=blockFeatures.end()){
         dumpBBFeatures(blockfile, bid, std::get<1>(*it), std::get<2>(*it),
    std::get<3>(*it));
       }
      }
    }*/
    /*for(auto &[bid,features,label]:blockFeatures){
      dumpBBFeatures(blockfile, bid, features, label);
    }*/
    std::sort(blockCFGRelationIds.begin(),blockCFGRelationIds.end());
    blockCFGRelationIds.erase(std::unique(blockCFGRelationIds.begin(),blockCFGRelationIds.end()),blockCFGRelationIds.end());
    //dbgs() << "CFG rel:" << blockCFGRelationIds.size() << "\n";
    for (auto &[sBid, dBid] : blockCFGRelationIds) {
      //if (std::find(soloBlocks.begin(), soloBlocks.end(), sBid) ==
        //  soloBlocks.end())
        //if (std::find(soloBlocks.begin(), soloBlocks.end(), dBid) ==
          //  soloBlocks.end())
          fprintf(blockrelfile, "%s;%s;%s;\n", std::to_string(sBid).c_str(), std::to_string(dBid).c_str(), "cfg");
    }

    dbgs() << "SVG rel:" << blockSVFRelationIds.size() << "\n";

    for (auto &[sBid, dBid, lbl] : blockSVFRelationIds) {
     // if (std::find(soloBlocks.begin(), soloBlocks.end(), sBid) ==
      //    soloBlocks.end())
       // if (std::find(soloBlocks.begin(), soloBlocks.end(), dBid) ==
         //   soloBlocks.end())
          fprintf(blockrelfile, "%s;%s;%s%s;\n", std::to_string(sBid).c_str(), std::to_string(dBid).c_str(), "svg",lbl.c_str());
    }
    dbgs() << "SCC rel:" << blockSCCRelationIds.size() << "\n";
    for (auto &[sBid, dBid] : blockSCCRelationIds) {
     // if (std::find(soloBlocks.begin(), soloBlocks.end(), sBid) ==
       //   soloBlocks.end())
       // if (std::find(soloBlocks.begin(), soloBlocks.end(), dBid) ==
         //   soloBlocks.end())
          fprintf(blockrelfile, "%s;%s;%s;\n", std::to_string(sBid).c_str(), std::to_string(dBid).c_str(), "scc");
    }

    // blockrelfile.close();
    // blockfile.close();
    fclose(blockrelfile);
    fclose(blockfile);

    llvm::dbgs() << "badblocks:" << badBlocks.size() << "\n";
    return false;
  }
  std::string getCleanBBContent(const llvm::BasicBlock *block) {
    /*if (block == nullptr){
      llvm::errs()<<"Null block found!";
      exit(1);
    }*/
    llvm::dbgs() << "-------------start of block "
                 << getUniqueBlockName(block, block->getParent())
                 << "---------------";
    for (auto &I : *block) {
      llvm::dbgs() << I.getOpcodeName() << "\n";
    }
    llvm::dbgs() << "-------------end of block "
                 << getUniqueBlockName(block, block->getParent())
                 << "---------------";
    return "";
  }
  std::string getInstLabel(const llvm::Instruction &inst) {
    if (inst.getMetadata("oh_hash")) {
      return "oh_hash";
    } else if (inst.getMetadata("oh_verify")) {
      return "oh_verify";
    } else if (inst.getMetadata("cfi_register")) {
      return "cfi_register";
    } else if (inst.getMetadata("cfi_verify")) {
      return "cfi_verify";
    } else if (inst.getMetadata("sc_guard")) {
      return "sc_guard";
    } else {
      return "none";
    }
  }
  void dumpBBFeatures(FILE *blockfile, const size_t BBId,
                      const std::vector<int> featureVector,std::string ModuleName, std::string BBLabel,
                      std::string BBContent) {
    fprintf(blockfile, "%zu;", BBId);
    for (int feature : featureVector) {
      fprintf(blockfile, "%i;", feature);
    }
    ModuleName = fs::path(ModuleName).filename();
    //llvm::errs() << ModuleName << "\n";
    //std::string cleanModule = std::regex_replace(ModuleName, std::regex("_(?:SC|OH|CFI|SUB|FLA|BCF|NONE|NA|i|a)"), "");
    std::string cleanModule = std::regex_replace(ModuleName, std::regex("_(?:NONE|NA|i|a)"), "");
    //llvm::errs() <<"clean:"<< cleanModule << "\n";
     
    fprintf(blockfile, "%s;%s;%s;\n\r", BBContent.c_str(), cleanModule.c_str(), BBLabel.c_str());
  }
  std::vector<std::tuple<std::size_t, std::size_t, std::string>>
  getOutEdgeBB(std::shared_ptr<pdg::FunctionPDG> fpdg, llvm::Value *I, llvm::Function *F,
               std::size_t blockId) {
    std::vector<std::tuple<std::size_t, std::size_t, std::string>> outBBEdges;
    if (!fpdg->hasNode(I)) {
      return outBBEdges;
    }
    auto *srcBB = llvm::dyn_cast<llvm::Instruction>(I)->getParent();
    auto node = fpdg->getNode(I);
    for (auto edge_it = node->outEdgesBegin();
         edge_it != node->outEdgesEnd(); ++edge_it) {
      pdg::PDGNode* destNode = (*edge_it)->getDestination().get();
      // Check if the edge is to or from another BB
      auto* llvmNode = llvm::dyn_cast<pdg::PDGLLVMNode>(destNode);
      if (!llvmNode) {
        continue;
      }
      auto nodeValue = llvmNode->getNodeValue();
      if (!nodeValue) {
            continue;
      }
      //llvm::dbgs() << "   Node value " << *nodeValue << "\n";
      // TODO: check this
      llvm::BasicBlock *nodeBB=nullptr;
      if (llvm::isa<pdg::PDGLLVMInstructionNode>(llvmNode)) {
	auto *destInst = llvm::dyn_cast<llvm::Instruction>(nodeValue);
        nodeBB = destInst->getParent();
      } else if  (llvm::isa<pdg::PDGLLVMBasicBlockNode>(llvmNode)) {
        nodeBB = llvm::dyn_cast<llvm::BasicBlock>(nodeValue);
      }
      if (nodeBB != nullptr && nodeBB!=srcBB) {
	    std::string edge_label = "c";
	    if((*edge_it).get()->isDataEdge()){
	      edge_label="d";
	    }
            outBBEdges.push_back(std::make_tuple(
                blockId, getUniqueBlockName(nodeBB, nodeBB->getParent()),edge_label));
        }
    }
    return outBBEdges;
  }
  int BBUniqueID = 101;
  std::size_t getUniqueBlockName(const llvm::BasicBlock *BB,
                                 const llvm::Function *F) {
    std::string Str = F->getParent()->getModuleIdentifier();
    Str += F->getName();
    std::string BBStr;
    /*if (!BB->getName().empty())
      BBStr = BB->getName().str();
    else*/
    //{
    // dbgs()<<"trying to print name\n";
    if (BB == nullptr) {
      errs() << "faulty BB\n";
      if (F == nullptr) {
        errs() << "Faulty function\n";
      } else {
        dbgs() << F->getName() << "\n";
      }
    }
    llvm::raw_string_ostream OS(BBStr);
    BB->printAsOperand(OS, false);
    BBStr = OS.str();
    // BBStr = std::to_string(BBUniqueID++);
    //}
    std::hash<std::string> hasher;
    auto hashed = hasher(Str + BBStr);
    return hashed;
  }
  std::vector<int> featureVector;
  void setFeature(const unsigned int featureIndex) {
    if (featureVector.size() == 0)
      for (int i = 0; i < 63; i++)
        featureVector.push_back(0);
    while (featureVector.size() < featureIndex + 1) {
      featureVector.push_back(0);
    }
    int &a = featureVector[featureIndex];
    // llvm::dbgs()<<"size:"<<featureVector.size()<<" a:"<<a<<"\n";
    a += 1;
  }
  void process(SVFG *svfg, llvm::Value *I) {
    auto *pag = svfg->getPAG();
    if (!pag->hasValueNode(I)) {
      // llvm::dbgs() << "   No PAG node\n";
      setFeature(0);
      return;
    }
    auto nodeId = pag->getValueNode(I);
    auto *pagNode = pag->getPAGNode(nodeId);
    // llvm::dbgs() << "   PAG Node " << *pagNode << "\n";

    setFeature(1);
    if (!hasIncomingEdges(pagNode) && !hasOutgoingEdges(pagNode)) {
      // llvm::dbgs() << "   No incoming or outgoing edges\n";
      setFeature(2);
      return;
    }
    processPAGNode(pagNode, svfg);
    if (auto *callInst = llvm::dyn_cast<llvm::CallInst>(I)) {
      setFeature(54);
      llvm::CallSite callSite(callInst);
      if (svfg->hasActualOUTSVFGNodes(callSite)) {
        //  llvm::dbgs() << "   Has actual out svfg nodes\n";
        setFeature(55);
        const auto &actualOutNodes = svfg->getActualOUTSVFGNodes(callSite);
        for (const auto &actualOut : actualOutNodes) {
          //  llvm::dbgs() << actualOut << "\n";
          setFeature(56);
          if (svfg->hasSVFGNode(actualOut)) {
            //  llvm::dbgs() << "svfg formal out " <<
            //  *svfg->getSVFGNode(actualOut)
            //             << "\n";
            setFeature(57);
          } else if (pag->hasGNode(actualOut)) {
            //    llvm::dbgs() << "pag formal out " <<
            //    *pag->getPAGNode(actualOut)
            //               << "\n";
            setFeature(58);
          }
        }
      }
      if (svfg->hasActualINSVFGNodes(callSite)) {
        // llvm::dbgs() << "   Has actual in svfg nodes\n";
        setFeature(59);
        const auto &actualInNodes = svfg->getActualINSVFGNodes(callSite);
        for (const auto &actualIn : actualInNodes) {
          //llvm::dbgs() << actualIn << "\n";
          setFeature(60);
          if (svfg->hasSVFGNode(actualIn)) {
            //   llvm::dbgs() << "svfg formal in " <<
            //   *svfg->getSVFGNode(actualIn)
            //              << "\n";
            setFeature(61);
          } else if (pag->hasGNode(actualIn)) {
            // llvm::dbgs() << "pag formal in " << *pag->getPAGNode(actualIn)
            //            << "\n";
            setFeature(62);
          }
        }
      }
    }
    // else if (auto* mssaPhi = llvm::dyn_cast<MSSAPHISVFGNode>(svfgNode)) {
    // }
  }

  void processPAGNode(PAGNode *node, SVFG *svfg) {
    if (!svfg->hasDef(node)) {
      setFeature(3);
      return;
    }
    auto *svfgNode = svfg->getDefSVFGNode(node);
    // llvm::dbgs() << "   SVFG node " << *svfgNode << "\n";
    setFeature(4);
    processSVFGNode(const_cast<SVFGNode *>(svfgNode), svfg);
    printEdges(svfgNode, svfg);
  }

  void processSVFGNode(SVFGNode *svfgNode, SVFG *svfg) {
    if (auto *stmtNode = llvm::dyn_cast<StmtSVFGNode>(svfgNode)) {
      setFeature(5);
      processStmtNode(const_cast<StmtSVFGNode *>(stmtNode), svfg);
    } else if (auto *actualParamNode =
                   llvm::dyn_cast<ActualParmSVFGNode>(svfgNode)) {
      //processActualParamNode(const_cast<ActualParmSVFGNode *>(actualParamNode),
      //                       svfg);
      setFeature(6);
    } else if (auto *actualRet = llvm::dyn_cast<ActualRetSVFGNode>(svfgNode)) {
      //processActualRetNode(const_cast<ActualRetSVFGNode *>(actualRet), svfg);
      setFeature(7);
    } else if (auto *formalParam =
                   llvm::dyn_cast<FormalParmSVFGNode>(svfgNode)) {
      processFormalParamNode(const_cast<FormalParmSVFGNode *>(formalParam),
                             svfg);
      setFeature(8);
    } else if (auto *formalRet = llvm::dyn_cast<FormalRetSVFGNode>(svfgNode)) {
      processFormalRetNode(const_cast<FormalRetSVFGNode *>(formalRet), svfg);
      setFeature(9);
    } else if (auto *formalInNode =
                   llvm::dyn_cast<FormalINSVFGNode>(svfgNode)) {
      //processFormalInNode(const_cast<FormalINSVFGNode *>(formalInNode), svfg);
      setFeature(10);
    } else if (auto *formalOutNode =
                   llvm::dyn_cast<FormalOUTSVFGNode>(svfgNode)) {
      //processFormalOutNode(const_cast<FormalOUTSVFGNode *>(formalOutNode),
      //                     svfg);
      setFeature(11);
    } else if (auto *actualInNode =
                   llvm::dyn_cast<ActualINSVFGNode>(svfgNode)) {
      //processActualInNode(const_cast<ActualINSVFGNode *>(actualInNode), svfg);
      setFeature(12);
    } else if (auto *actualOutNode =
                   llvm::dyn_cast<ActualOUTSVFGNode>(svfgNode)) {
      //processActualOutNode(const_cast<ActualOUTSVFGNode *>(actualOutNode),
      //                     svfg);
      setFeature(13);
    } else if (auto *intraMssaPhiNode =
                   llvm::dyn_cast<IntraMSSAPHISVFGNode>(svfgNode)) {
      processIntraMssaPhiNode(
          const_cast<IntraMSSAPHISVFGNode *>(intraMssaPhiNode), svfg);
      setFeature(14);
    } else if (auto *interMssaPhiNode =
                   llvm::dyn_cast<InterMSSAPHISVFGNode>(svfgNode)) {
      processInterMssaPhiNode(
          const_cast<InterMSSAPHISVFGNode *>(interMssaPhiNode), svfg);
      setFeature(15);
    } else if (auto *null = llvm::dyn_cast<NullPtrSVFGNode>(svfgNode)) {
      //llvm::dbgs() << "       Null Node\n";
      setFeature(16);
    } else if (auto *intraPhiNode =
                   llvm::dyn_cast<IntraPHISVFGNode>(svfgNode)) {
      processIntraPhiNode(const_cast<IntraPHISVFGNode *>(intraPhiNode), svfg);
      setFeature(17);
    } else if (auto *interPhiNode =
                   llvm::dyn_cast<InterPHISVFGNode>(svfgNode)) {
      processInterPhiNode(const_cast<InterPHISVFGNode *>(interPhiNode), svfg);
      setFeature(18);
    }
  }

  void printEdges(const SVFGNode *svfgNode, SVFG *svfg) {
    // llvm::dbgs() << "INCOMING EDGES\n";
    for (auto inedge_it = svfgNode->InEdgeBegin();
         inedge_it != svfgNode->InEdgeEnd(); ++inedge_it) {
      setFeature(19);
      printEdge(svfgNode, *inedge_it, svfg, true);
    }
    // llvm::dbgs() << "OUT EDGES\n";
    for (auto edge_it = svfgNode->OutEdgeBegin();
         edge_it != svfgNode->OutEdgeEnd(); ++edge_it) {
      setFeature(20);
      printEdge(svfgNode, *edge_it, svfg, false);
    }
  }

  void printEdge(const SVFGNode *svfgNode, SVFGEdge *edge, SVFG *svfg,
                 bool incoming) {
    // llvm::dbgs() << "   Edge type ";
    auto edgeKind = edge->getEdgeKind();
    if (edgeKind == SVFGEdge::IntraDirect) {
      setFeature(21);
      // llvm::dbgs() << "IntraDirect\n";
    } else if (edgeKind == SVFGEdge::IntraIndirect) {
      setFeature(22);
      // llvm::dbgs() << "IntraIndirect\n";
    } else if (edgeKind == SVFGEdge::DirCall) {
      setFeature(22);
      //  llvm::dbgs() << "DirCall\n";
    } else if (edgeKind == SVFGEdge::DirRet) {
      setFeature(23);
      //  llvm::dbgs() << "DirRet\n";
    } else if (edgeKind == SVFGEdge::IndCall) {
      setFeature(24);
      // llvm::dbgs() << "IndCall\n";
    } else if (edgeKind == SVFGEdge::IndRet) {
      setFeature(25);
      //  llvm::dbgs() << "IndRet\n";
    } else if (edgeKind == SVFGEdge::TheadMHPIndirect) {
      setFeature(26);
      //  llvm::dbgs() << "TheadMHPIndirect\n";
    }
    SVFGNode *node = nullptr;

    if (incoming) {
      node = edge->getSrcNode();
      // llvm::dbgs() << "       Edge Src node\n";
    } else {
      node = edge->getDstNode();
      // llvm::dbgs() << "       Edge Dst node\n";
    }

    // Check if the edge is to or from another BB
    if (svfgNode->getBB() != node->getBB()) {
      setFeature(27);
      // llvm::dbgs() <<"        Edge to/from another BB \n";
    }
    processSVFGNode(const_cast<SVFGNode *>(node), svfg);
  }

  void processStmtNode(StmtSVFGNode *stmtNode, SVFG *svfg) {
    if (stmtNode->getInst()) {
      //  llvm::dbgs() << "       Stmt Node " << *stmtNode->getInst() << "\n";
      setFeature(28);
    }
    SVFGNode *defNode = nullptr;
    if (auto *addrNode = llvm::dyn_cast<AddrSVFGNode>(stmtNode)) {
      setFeature(29);
      if (svfg->hasDef(addrNode->getPAGSrcNode())) {
        setFeature(30);
        defNode = const_cast<SVFGNode *>(
            svfg->getDefSVFGNode(addrNode->getPAGSrcNode()));
      }
    } else if (auto *cpyNode = llvm::dyn_cast<CopySVFGNode>(stmtNode)) {
      setFeature(31);
      if (svfg->hasDef(cpyNode->getPAGSrcNode())) {
        setFeature(32);
        defNode = const_cast<SVFGNode *>(
            svfg->getDefSVFGNode(cpyNode->getPAGSrcNode()));
      }
    } else if (auto *gepNode = llvm::dyn_cast<GepSVFGNode>(stmtNode)) {
      setFeature(33);
      if (svfg->hasDef(gepNode->getPAGSrcNode())) {
        setFeature(34);
        defNode = const_cast<SVFGNode *>(
            svfg->getDefSVFGNode(gepNode->getPAGSrcNode()));
      }
    } else if (auto *loadNode = llvm::dyn_cast<LoadSVFGNode>(stmtNode)) {
      setFeature(35);
      if (svfg->hasDef(loadNode->getPAGSrcNode())) {
        setFeature(36);
        defNode = const_cast<SVFGNode *>(
            svfg->getDefSVFGNode(loadNode->getPAGSrcNode()));
      }
    } else if (auto *storeNode = llvm::dyn_cast<StoreSVFGNode>(stmtNode)) {
      setFeature(37);
      // llvm::dbgs() << "Store node\n";
    }
    if (defNode) {
      setFeature(38);
      // llvm::dbgs() << "Def node: " << *defNode << "\n";
    }
  }

  void processActualParamNode(ActualParmSVFGNode *actualParamNode, SVFG *svfg) {
    // llvm::dbgs() << "       Actual param node\n";
    // llvm::dbgs() << "       Call site "
    //            << *(actualParamNode->getCallSite().getInstruction()) << "\n";
    // llvm::dbgs() << "       Param " << *actualParamNode->getParam() << "\n";
    auto *pagNode = actualParamNode->getParam();
    // processPAGNode(const_cast<PAGNode *>(pagNode), svfg);
  }

  void processActualRetNode(ActualRetSVFGNode *actualRetNode, SVFG *svfg) {
    // llvm::dbgs() << "       Actual ret node\n";
    // llvm::dbgs() << "       Call site "
    //            << *(actualRetNode->getCallSite().getInstruction()) << "\n";
    // llvm::dbgs() << "       Rev " << *actualRetNode->getRev() << "\n";
    auto *pagNode = actualRetNode->getRev();
    // processPAGNode(const_cast<PAGNode *>(pagNode), svfg);
  }

  void processFormalParamNode(FormalParmSVFGNode *formalParamNode, SVFG *svfg) {
    // llvm::dbgs() << "       Formal param node\n";
    // llvm::dbgs() << "       Function " <<
    // formalParamNode->getFun()->getName()
    //            << "\n";
    // llvm::dbgs() << "       Param " << *formalParamNode->getParam() << "\n";
    for (auto it = formalParamNode->callPEBegin();
         it != formalParamNode->callPEEnd(); ++it) {
      setFeature(39);
      // llvm::dbgs() << "       callPE callSite " << *((*it)->getCallInst())
      //            << "\n";
      // llvm::dbgs() << "       source node " << *(*it)->getSrcNode() << "\n";
      // llvm::dbgs() << "       dest node " << *(*it)->getDstNode() << "\n";
      // processPAGNode(const_cast<PAGNode *>((*it)->getSrcNode()), svfg);
    }
  }

  void processFormalRetNode(FormalRetSVFGNode *formalRetNode, SVFG *svfg) {
    //  llvm::dbgs() << "       Formal ret node\n";
    // llvm::dbgs() << "       Function " << formalRetNode->getFun()->getName()
    //             << "\n";
    // llvm::dbgs() << "       Ret " << *formalRetNode->getRet() << "\n";
    for (auto it = formalRetNode->retPEBegin(); it != formalRetNode->retPEEnd();
         ++it) {
      setFeature(40);
      //  llvm::dbgs() << "       retPE callSite " << *(*it)->getCallInst() <<
      //  "\n";
      // llvm::dbgs() << "       source node " << *(*it)->getSrcNode() << "\n";
      // llvm::dbgs() << "       dest node " << *(*it)->getDstNode() << "\n";
    }
    // No def for FormalRet node
  }

  void processFormalInNode(FormalINSVFGNode *formalInNode, SVFG *svfg) {
    //    llvm::dbgs() << "       Formal IN node\n";
    //   llvm::dbgs() << "       Entry CHI ";
    const_cast<EntryCHI<DdNode *> *>(formalInNode->getEntryChi())->dump();
    // llvm::dbgs() << "       Res Ver def \n";
    const_cast<MSSADEF *>(formalInNode->getEntryChi()->getResVer()->getDef())
        ->dump();
    // llvm::dbgs() << "       Res Ver mem region \n";
    formalInNode->getEntryChi()->getResVer()->getMR()->dumpStr();
    //   llvm::dbgs() << "       Op Ver def\n";
    const_cast<MSSADEF *>(formalInNode->getEntryChi()->getOpVer()->getDef())
        ->dump();
    //  llvm::dbgs() << "       Op Ver mem region \n";
    formalInNode->getEntryChi()->getOpVer()->getMR()->dumpStr();
  }

  void processFormalOutNode(FormalOUTSVFGNode *formalOutNode, SVFG *svfg) {
    // llvm::dbgs() << "       Formal OUT node\n";
    // llvm::dbgs() << "       Ret MU \n";
    const_cast<RetMU<DdNode *> *>(formalOutNode->getRetMU())->dump();
    // Has PointsTo
  }

  void processActualInNode(ActualINSVFGNode *actualInNode, SVFG *svfg) {
    //  llvm::dbgs() << "       Actual IN node\n";
    //  llvm::dbgs() << "       Call MU \n";
    const_cast<CallMU<DdNode *> *>(actualInNode->getCallMU())->dump();
    // Has PointsTo
  }

  void processActualOutNode(ActualOUTSVFGNode *actualOutNode, SVFG *svfg) {
    // llvm::dbgs() << "       Actual OUT node\n";
    // llvm::dbgs() << "       Call CHI \n";
    const_cast<CallCHI<DdNode *> *>(actualOutNode->getCallCHI());
    // llvm::dbgs() << "       Op Ver def\n";
    const_cast<MSSADEF *>(actualOutNode->getCallCHI()->getOpVer()->getDef())
        ->dump();
    //  llvm::dbgs() << "       Op Ver mem region \n";
    actualOutNode->getCallCHI()->getMR()->dumpStr();
  }

  void processIntraMssaPhiNode(IntraMSSAPHISVFGNode *intraMssaPhiNode,
                               SVFG *svfg) {
    std::unordered_set<MSSADEF *> defs;
    auto *res_def = const_cast<MSSADEF *>(intraMssaPhiNode->getRes());
    if (!defs.insert(res_def).second) {
      return;
    }
    //  llvm::dbgs() << "       Intra MSSA phi node\n";
    //  llvm::dbgs() << "       Res \n";
    //  res_def->dump();
    //llvm::dbgs() << intraMssaPhiNode->getOpVerNum() << "\n";
    for (auto it = intraMssaPhiNode->opVerBegin();
         it != intraMssaPhiNode->opVerEnd(); ++it) {
      auto *def = it->second->getDef();
      //   llvm::dbgs() << "       op ver def \n";
      setFeature(41);
      processMSSADef(def, defs);
      // const_cast< MSSADEF*>(def)->dump();
      // llvm::dbgs() << "       Op Ver mem region " << def->getMR()->dumpStr()
      // << "\n";
    }
  }

  void processMSSADef(MSSADEF *def, std::unordered_set<MSSADEF *> &defs) {
    if (!defs.insert(def).second) {
      setFeature(42);
      return;
    }
    if (def->getType() == MSSADEF::CallMSSACHI) {
      auto *callChi = llvm::dyn_cast<SVFG::CALLCHI>(def);
      setFeature(43);
      //     llvm::dbgs() << "           Call CHI ";
      //callChi->dump();
    } else if (def->getType() == MSSADEF::StoreMSSACHI) {
      auto *storeChi = llvm::dyn_cast<SVFG::STORECHI>(def);
      setFeature(44);
      //   llvm::dbgs() << "           Store CHI "
      //               << *storeChi->getStoreInst()->getInst() << "\n";
    } else if (def->getType() == MSSADEF::EntryMSSACHI) {
      setFeature(45);
      //   llvm::dbgs() << "           Entry Chi\n";
    } else if (def->getType() == MSSADEF::SSAPHI) {
      auto *phi = llvm::dyn_cast<MemSSA::PHI>(def);
      setFeature(46);
      //  llvm::dbgs() << "           Phi\n";
      for (auto it = phi->opVerBegin(); it != phi->opVerEnd(); ++it) {
        setFeature(47);
        processMSSADef(it->second->getDef(), defs);
      }
    }
  }

  void processInterMssaPhiNode(InterMSSAPHISVFGNode *interMssaPhiNode,
                               SVFG *svfg) {
    //  llvm::dbgs() << "       Inter MSSA phi node\n";
    //   llvm::dbgs() << "       Res\n";
    const_cast<MSSADEF *>(interMssaPhiNode->getRes())->dump();
    setFeature(48);
    for (auto it = interMssaPhiNode->opVerBegin();
         it != interMssaPhiNode->opVerEnd(); ++it) {
      //   llvm::dbgs() << "       op ver def \n";
      setFeature(49);
      const_cast<MSSADEF *>(it->second->getDef())->dump();
      //  llvm::dbgs() << "       Op Ver mem region \n";
      it->second->getMR()->dumpStr();
    }
  }

  void processIntraPhiNode(IntraPHISVFGNode *intraPhiNode, SVFG *svfg) {
    // llvm::dbgs() << "       Intra PHI node\n";
    //  llvm::dbgs() << "       Res " << *intraPhiNode->getRes() << "\n";
    setFeature(50);
    for (auto it = intraPhiNode->opVerBegin(); it != intraPhiNode->opVerEnd();
         ++it) {
      setFeature(51);
      //    llvm::dbgs() << "       op ver: " << *it->second << "\n";
    }
  }

  void processInterPhiNode(InterPHISVFGNode *interPhiNode, SVFG *svfg) {
    // llvm::dbgs() << "   Inter PHI node\n";
    //  llvm::dbgs() << "       Res " << *interPhiNode->getRes() << "\n";
    setFeature(52);
    for (auto it = interPhiNode->opVerBegin(); it != interPhiNode->opVerEnd();
         ++it) {
      setFeature(53);
      //  llvm::dbgs() << "       op ver: " << *it->second << "\n";
    }
  }
};

char PDGCSV::ID = 0;
static llvm::RegisterPass<PDGCSV>
    X("pdg-csv", "Traverse SVFG graph and print information in CSV");

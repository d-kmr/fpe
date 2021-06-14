/*
Analyzer module of FPE
*/


#include "SVF-FE/LLVMUtil.h"
#include "Graphs/SVFG.h"
#include "WPA/Andersen.h"
#include "SABER/LeakChecker.h"
#include "SVF-FE/PAGBuilder.h"

using namespace SVF;
using namespace llvm;
using namespace std;

std::string _Quote = "\"";
std::string _Comma = ", ";
std::string _None = "";
std::string _NewLine = "\n";
std::string _CommaNewLine = ",\n";

std::string addQuote(const std::string str){
  return "\"" + str + "\"";
}

// To display a value
void peekValue(const llvm::Value *val)
{
  if (val == NULL){ cout << "It's NULL!\n"; return; }
  std::string str;
  raw_string_ostream rawstr(str);
  val->print(rawstr);
  cout << rawstr.str() << "\n";
  return;
}

void peekNode(PAGNode* node)
{
  if (node == NULL) { cout << "NullNode!\n"; return; }
  const llvm::Value* val = node->getValue();
  peekValue(val);
  return;
}

// Node0x557e1d09ad30 [shape=record,shape=circle,label="{[main] ValPN ID: 4294967227   %f = getelementptr inbounds %struct.A, %struct.A* %8, i32 0, i32 4 \{  \}}"];

// stringVector: it returns a string of the given string list
// l: the left additional string of each element 
// r: the right additional string of each element
// e.g. aaa -> [aaa], if l and r are [ and ]
// sep: the separation symbol
// last: the lastly added symbol
std::string stringVector(std::vector<std::string> v, std::string l, std::string r, std::string sep, std::string last)
{
  std::string str;
  raw_string_ostream rawstr(str);
  for (std::vector<std::string>::iterator ii=v.begin(), ie=v.end(); ii != ie; ii++)
	{
	  if (ii != v.begin()) rawstr << sep;
	  rawstr << l << *ii << r;
	}
  rawstr << last;
  return rawstr.str();
}


//-----------------------------------------------
// Internal data structure for FPdata
//-----------------------------------------------
typedef enum FPkind { NoInfo, Var, ArrPtr, Ptr, Arr } FPkind;

std::string kind2str(FPkind k)
{
  std::string res;
  switch(k)
	{
	case Var:    res = "_"; break;
	case Ptr:    res = "P"; break;
	case Arr:    res = "A"; break;
	case ArrPtr: res = "AP"; break;
	default:     res = "NoInfo";
	}
  return(res);
}

std::string tagFPFLD = addQuote("FPFLD");
std::string tagFPVAR = addQuote("FPVAR");
std::string tagFPARR = addQuote("FPARR");
std::string keyName = addQuote("name");
std::string keyTp = addQuote("tp");
std::string keyFldName = addQuote("fld_name");
std::string keyFldIndex = addQuote("fld_index");
std::string keyKind = addQuote("kind");
std::string keyInFun = addQuote("in_fun");
std::string keyToFuns = addQuote("to_funs");
std::string keyPtr = addQuote("ptr");
std::string keyFld = addQuote("fld");
std::string colon = ":";
std::string comma = ", ";

std::string mkJSON (string name,FPkind kind,vector<string> flds,string inFun,vector<string> toFuns)
{
  string str;
  raw_string_ostream rawstr(str);
  
  if (flds.size() == 0 && kind == Var) // FPVAR case
	{
	  // put tagFPVAR here
	  rawstr << "[" + tagFPVAR + comma + "{";
	  rawstr << keyName + colon + addQuote(name);
	  rawstr << comma;
	  rawstr << keyInFun + colon + addQuote(inFun);
	  rawstr << comma;
	  rawstr << keyToFuns + colon + "[" << stringVector(toFuns,_Quote,_Quote,_Comma,_None) << "] ";
	  rawstr << "}]";
	  return (rawstr.str());
	}

  if (flds.size() == 0 && kind == Arr) // FPARR case
	{
	  // put tagFPARR here
	  rawstr << "[" + tagFPARR + comma + "{";
	  rawstr << keyPtr + colon + addQuote(name);
	  rawstr << comma;	  
	  rawstr << keyInFun + colon + addQuote(inFun);
	  rawstr << comma;		
	  rawstr << keyToFuns + colon + "[" << stringVector(toFuns,_Quote,_Quote,_Comma,_None) << "] ";
	  rawstr << "}]";
	  return (rawstr.str());
	}

  // put tagFPFLD here
  // FPFLD case
  rawstr << "[" + tagFPFLD + comma + "{";
  rawstr << keyPtr + colon + addQuote(name);
  rawstr << comma;
  rawstr << keyKind + colon + addQuote(kind2str(kind));
  rawstr << comma;  
  rawstr << keyFld + colon + "[" << stringVector(flds,_None,_None,_Comma,_None) << "]";
  rawstr << comma;  
  rawstr << keyInFun + colon + addQuote(inFun);
  rawstr << comma;
  rawstr << keyToFuns + colon + "[" << stringVector(toFuns,_Quote,_Quote,_Comma,_None) << "] ";
  rawstr << "}]";
  return (rawstr.str());
}

std::string checkTypeOfValue(const llvm::Value *val){
  llvm::Type* ty = val->getType();
  if (ty->isVoidTy ())		return "Void";
  if (ty->isHalfTy ())		return "Half";
  if (ty->isFloatTy ())		return "32-bit float";
  if (ty->isDoubleTy ())	return "64-bit float";
  if (ty->isX86_FP80Ty ())	return "x86 long double";
  if (ty->isFP128Ty ())		return "128-bit float";
  if (ty->isPPC_FP128Ty ()) return "powerpc long double";
  if (ty->isFloatingPointTy ())   return "six floating-point";
  if (ty->isX86_MMXTy ())	return "X86-MMX";
  if (ty->isFPOrFPVectorTy ())	return "FP-type or Vector of FP";
  if (ty->isLabelTy ())		return "Label";
  if (ty->isMetadataTy ())	return "metadata";
  if (ty->isTokenTy ())		return "token";
  if (ty->isIntegerTy ())	return "Integer";
  if (ty->isIntOrIntVectorTy ())  return "integer or vector of int";
  if (ty->isIntOrPtrTy ())	return "int or pointer";
  if (ty->isFunctionTy ())	return "Function";
  if (ty->isStructTy ())	return "Struct";
  if (ty->isArrayTy ())		return "Array";
  if (ty->isPointerTy ())	return "Pointer";
  if (ty->isPtrOrPtrVectorTy ())  return "Pointer or vector of pointers";
  if (ty->isVectorTy ())   return "Vector";
  return "Other";
}

void checkIncommingEdge(PAGNode* node)
{ // Addr, Copy, Store, Load, Call, Ret, NormalGep, VariantGep, ThreadFork, ThreadJoin, Cmp, BinaryOp, UnaryOp  
  if(*(node->getIncomingEdges(PAGEdge::Addr).begin()) != NULL) cout << "Addr";
  if(*(node->getIncomingEdges(PAGEdge::Copy).begin()) != NULL) cout << "Copy";	// black edge
  if(*(node->getIncomingEdges(PAGEdge::Store).begin()) != NULL) cout << "Store"; 
  if(*(node->getIncomingEdges(PAGEdge::Load).begin()) != NULL) cout << "Load"; 	 // red edge
  if(*(node->getIncomingEdges(PAGEdge::Call).begin()) != NULL) cout << "Call";
  if(*(node->getIncomingEdges(PAGEdge::Ret).begin()) != NULL) cout << "Ret";	
  if(*(node->getIncomingEdges(PAGEdge::NormalGep).begin()) != NULL) cout << "NGep"; // purple edge
  if(*(node->getIncomingEdges(PAGEdge::VariantGep).begin()) != NULL) cout << "VGep";
  if(*(node->getIncomingEdges(PAGEdge::ThreadFork).begin()) != NULL) cout << "Fork";
  if(*(node->getIncomingEdges(PAGEdge::ThreadJoin).begin()) != NULL) cout << "Join";
  if(*(node->getIncomingEdges(PAGEdge::Cmp).begin()) != NULL) cout << "Cmp";
  if(*(node->getIncomingEdges(PAGEdge::BinaryOp).begin()) != NULL) cout << "Bop";
  if(*(node->getIncomingEdges(PAGEdge::UnaryOp).begin()) != NULL) cout << "Uop";
  return;
}

std::string checkInstruction(const llvm::Instruction *inst)
{
  if(inst==NULL) return "";
  if(inst->isTerminator ())		return "Terminator";
  if(inst->isUnaryOp ())		return "UnaryOp";
  if(inst->isBinaryOp ())		return "BinaryOp";
  if(inst->isIntDivRem ())		return "IntDivRem";
  if(inst->isShift ())			return "Shift";
  if(inst->isCast ())			return "Cast";
  if(inst->isFuncletPad ())		return "FuncletPad";
  if(inst->isExceptionalTerminator ())		return "ExceptionalTerminator";
  if(inst->isIndirectTerminator ())		return "IndirectTerminator";
  if(inst->isLogicalShift ())	return "LogicalShift";
  if(inst->isArithmeticShift ())return "ArithShift";
  if(inst->isBitwiseLogicOp ())	return "BitwiseLogicOp";
  return "Other";
}	

std::string checkNodeType(PAGNode* node)
{
  if(node == NULL) return "";
  const llvm::Instruction* inst = dyn_cast<Instruction>(node->getValue());
  const llvm::GlobalValue* glob = dyn_cast<GlobalValue>(node->getValue());
  if(inst != NULL)
	{
	  std::string opCodeName = inst->getOpcodeName();
	  if(opCodeName == "load") return("LOAD");
	  if(opCodeName == "alloca") return("ALLOCA");
	  if(opCodeName == "getelementptr") return("GEP");
	  if(opCodeName == "common") return("COMMON");  
	  return("OTHER");
	}
  else if(glob != NULL)
	{
	  return("GLOBAL");
	}
  return "";
}

PAGNode* getParentNode(PAGNode* node, PAGEdge::PEDGEK edgeKind)
{
  PAGEdge::PAGEdgeSetTy::iterator edge = node->getIncomingEdges(edgeKind).begin();
  if(*edge == NULL) return(NULL);
  return (*edge)->getSrcNode();
}				   







// Getting the distination node of a LOAD edge from 'node'
// If 'node' doesn't have a LOAD edge, this returns NULL
std::vector<PAGNode*> getLoadDist(PAGNode* node)
{
  std::vector<PAGNode*> nodes;
  PAGEdge::PAGEdgeSetTy edgeItr = node->getOutgoingEdges(PAGEdge::Load); 
  for (auto edge = edgeItr.begin(), iend = edgeItr.end(); edge != iend; edge++)
	{
	  if(*edge == NULL) continue;
	  nodes.push_back ((*edge)->getDstNode());
	}
  return (nodes);  
}

// 'node' is a pointer node if it is a source node of a Load edge
bool isPtrNode(PAGNode* node)
{
  std::vector<PAGNode*> nodes = getLoadDist(node);
  return (nodes.size() != 0);
}

std::vector<PAGNode*> getGepDists(PAGNode* node)
{
  std::vector<PAGNode*> nodes;
  
  return(nodes);
}

// Get the TopNode (start node for obtaining fpcall info) of given node
// TopNode is ALLOCA for local variables, COMMON for global variables
PAGNode* getTopNode(PAGNode* node)
{
  PAGEdge::PAGEdgeSetTy::iterator edge1,edge2,edge;  
  PAGNode* nd = node;
  
  while (nd != NULL && checkNodeType(nd) != "ALLOCA" && checkNodeType(nd) != "GLOBAL")
	{
	  edge1 = nd->getIncomingEdges(PAGEdge::NormalGep).begin();
	  edge2 = nd->getIncomingEdges(PAGEdge::Load).begin();
	  if (*edge1 == NULL && *edge2 == NULL) return(NULL);
	  edge = (*edge1 != NULL) ? edge1 : edge2;
	  nd = (*edge)->getSrcNode();
	}
  
  return(nd);
}


typedef enum { UNKNOWN, FPVAR, FPARR, FPFLDptr, FPFLDobj } NodeKind;

NodeKind checkNodeKind(PAGNode* node)
{
  if (node == NULL) return (UNKNOWN);
  SVF::PAGEdge::PAGEdgeSetTy loadEdgeItr = node->getOutgoingEdges(PAGEdge::Load);
  SVF::PAGEdge::PAGEdgeSetTy  gepEdgeItr = node->getOutgoingEdges(PAGEdge::NormalGep);

  if (loadEdgeItr.size() != 0)
	{
	  std::vector<PAGNode*> nodes = getLoadDist(node);
	  if (nodes[0]->getOutgoingEdges(PAGEdge::NormalGep).size() == 0)
		return (FPVAR);
	  else
		return (FPFLDptr);
	}

  for (auto iter = gepEdgeItr.begin(), iend = gepEdgeItr.end(); iter != iend; iter++)
	{
	  PAGNode* nd = (*iter)->getDstNode();
	  std::string name = nd->getValue()->getName().str();
	  if (name.find("arrayidx") != std::string::npos
		  && getLoadDist(nd).size() > 0
		  && getLoadDist(nd)[0]->getOutgoingEdges(PAGEdge::NormalGep).size() == 0)
		return (FPARR);
	}
  
  return (FPFLDobj);
}

// FPkind Arr    is X[-].fld*() : %arrayidx=gep%X <-GEP- %X=alloca -GEP-> %fld=load%arrayidx -Load-> ...
// FPkind Ptr    is X->fld*()   : %X=alloca -Load-> %20=load%X -GEP-> %fld=gep%20 ...
// FPkind ArrPtr is X[-]->fld*(): %X=alloca -GEP-> %arrayidx=load%X -Load-> %20=load%arrayidx -GEP-> %fld=gep%20
// FPkind Var    is X.fld*()    : %X=alloca -GEP-> (not %arrayidx node)
FPkind getTopFpKind(PAGNode* node)
{
  bool arrFlag = false;
  bool arrptrFlag = false;
  if (node == NULL) return (NoInfo);
  
  SVF::PAGEdge::PAGEdgeSetTy loadEdgeItr = node->getOutgoingEdges(PAGEdge::Load);
  SVF::PAGEdge::PAGEdgeSetTy  gepEdgeItr = node->getOutgoingEdges(PAGEdge::NormalGep);

  if (loadEdgeItr.size() != 0) return(Ptr);

  for (auto iter = gepEdgeItr.begin(), iend = gepEdgeItr.end(); iter != iend; iter++)
	{
	  PAGNode* nd = (*iter)->getDstNode();
	  std::string name = nd->getValue()->getName().str();
	  if (name.find("arrayidx") != std::string::npos
		  && getLoadDist(nd).size() > 0
		  && getLoadDist(nd)[0]->getOutgoingEdges(PAGEdge::NormalGep).size() > 0)
		arrptrFlag = true;
	  if (name.find("arrayidx") != std::string::npos && getLoadDist(nd).size() == 0)		  
		arrFlag = true;
	}
  FPkind res = arrptrFlag ? ArrPtr : (arrFlag ? Arr : Var);
  return (res);
}

std::string getPrevPointer(PAGNode* node)
{
  const llvm::Value* val = node->getValue();
  const llvm::GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(val);
  const llvm::LoadInst* loadInst = dyn_cast<LoadInst>(val);
  std::string ptr;

  if(loadInst != NULL){
	ptr = loadInst->getPointerOperand()->getName().str();
	return(ptr);
  }
  
  if(gepInst != NULL){
	ptr = gepInst->getPointerOperand()->getName().str();
	return(ptr);
  }

  return("dummy");
}

// Finding a next gep node
// bottom-up creating of a field info
void nextGep(PAGNode** gepNodeP, FPkind* kindP, PAGNode* topNode)
{
  PAGNode* curNode = *gepNodeP;
  std::string topName = topNode->getValue()->getName().str();  
  std::string subgoal = curNode->getValue()->getName().str();  
  bool ptrFlag = false;
  bool arrFlag = false;
  
  while(true) // curNode is a gep-node or a load-node && subgoal = curName
	{
	  subgoal = getPrevPointer(curNode);
	  if(subgoal.find("arrayidx") != std::string::npos) { arrFlag = true; }
	  if(subgoal == topName) { *gepNodeP = NULL; *kindP = NoInfo; return; }
	  if(dyn_cast<LoadInst>(curNode->getValue()) != NULL)
		{
		  curNode = getParentNode(curNode, PAGEdge::Load);
		  ptrFlag = true;
		  break;
		}
	  curNode = getParentNode(curNode, PAGEdge::NormalGep);
	  std::string curName = curNode->getValue()->getName().str();
	  if(curName == subgoal){ continue; }	  
	  PAGEdge::PAGEdgeSetTy edgeItr = curNode->getOutgoingEdges(PAGEdge::NormalGep);
	  
	  for (auto edge = edgeItr.begin(), iend = edgeItr.end(); edge != iend; edge++)
		{
		  if(*edge == NULL) { cout << "Something unexpected happens!"; exit(0); }
		  PAGNode* dst = (*edge)->getDstNode();
		  if(subgoal == dst->getValue()->getName().str())
			{
			  curNode = dst;
			  break;
			}
		}
	  if(subgoal.find("arrayidx") == std::string::npos) break;
	}
  *gepNodeP = curNode;  
  *kindP = ptrFlag ? (arrFlag ? ArrPtr : Ptr) : (arrFlag ? Arr : Var);
  return;
}

std::string createFldOne(PAGNode* node,FPkind kind)
{
  // making fld_index
  const llvm::GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(node->getValue());
  if(gep == NULL) { cout << "Unexpected case\n"; return(""); }
  std::string fld;
  raw_string_ostream rawstr(fld);
  auto ii = gep->idx_begin();
  ii++;
  llvm::Value* fldPosValue = *ii;
  fldPosValue->print(rawstr); // field position, like "i32 5" (5-th pos)
  std::string fldIndex = rawstr.str().substr(4); // "i32 5" --> "5"

  // making fld_name
  std::string fldName = node->getValue()->getName().str();

  // making tp
  llvm::Type* tp = gep->getSourceElementType();  
  std::string strTpName = (tp->isStructTy()) ? dyn_cast<StructType>(tp)->getName().str() : "NoType";

  std::string fldOne = "{"
	+ keyTp + colon + addQuote(strTpName) + ","
	+ keyFldName + colon + addQuote(fldName) + ","
	+ keyFldIndex + colon + fldIndex + ","
	+ keyKind + colon + addQuote(kind2str(kind))
	+ "}";

  return (fldOne);
}

// Creating Fields (main part)
void createFlds(PAGNode* fpNode, PAGNode* topNode, std::vector<string>* fldsP)
{
  PAGNode* node = getParentNode(fpNode,PAGEdge::Load); // GEP node
  FPkind kind = Ptr;  // initial fp should be a pointer
  std::string fld = createFldOne(node,kind);
  (*fldsP).push_back(fld);
  
  while(true)
	{	  
	  nextGep(&node,&kind,topNode);
	  if(node == NULL) break; // when no nextGep
	  std::string fld1 = createFldOne(node,kind);
	  (*fldsP).push_back(fld1);
	}
  return;
}

int main(int argc, char ** argv)
{
  // argment processing for SVF
  int arg_num = 0;
  char **arg_value = new char*[argc];
  std::vector<std::string> moduleNameVec;
  SVFUtil::processArguments(argc, argv, arg_num, arg_value, moduleNameVec);
  SVFModule* svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(moduleNameVec);  
	
  /// Build Program Assignment Graph (PAG)
  PAGBuilder builder;
  PAG *pag = builder.build(svfModule);

  /// Create Andersen's pointer analysis
  Andersen *ander = AndersenWaveDiff::createAndersenWaveDiff(pag);

  const PAG::CallSiteToFunPtrMap& aaa = pag->getIndirectCallsites();
  NodeID fpNodeID;
  std::string headStr, tailStr, inFun;
  PAGNode *fpNode, *refNode;
  std::vector<std::string> result;
  std::vector<std::string> jsonResult;

  for (auto iter = aaa.begin(), iend = aaa.end(); iter != iend; iter++)
	{
	  // Result
	  std::string res;
	  raw_string_ostream rawstr(res);
	  std::vector<std::string> head, flds, getCurrentNameResult;
	  
	  // function pointer load node for fpcall, like %20 = load %fp2
	  fpNodeID = (*iter).second;
	  fpNode = pag->getPAGNode(fpNodeID);
	  
	  // Making in-fun
	  string inFun = (fpNode != NULL && fpNode->getFunction() != NULL) ? fpNode->getFunction()->getName().str() : "FAILED-TO-GET_INFUN";
	  
	  // Getting function values for fpNode from the SVF analysis result
	  const NodeBS& fpPts = ander->getPts(fpNodeID); // iterator	  
	  PAGNode* fpPagNode = ander->getPAG()->getPAGNode(*fpPts.begin());
	  // Checking: Skip if the tail-part contains a non-function node	  
	  if (fpPagNode == NULL
		  || !fpPagNode->hasValue()
		  || fpPagNode->getType() == NULL
		  || fpPagNode->getType()->getTypeID() != llvm::Type::FunctionTyID)
		continue;

	  // Making toFuns
	  vector<string> toFuns;	  
	  for (NodeBS::iterator ii=fpPts.begin(), ie=fpPts.end() ; ii != ie; ++ii)
		{
		  PAGNode* node = ander->getPAG()->getPAGNode(*ii);
		  if(node->hasValue())
			{
			  const std::string funName = node->getValue()->getName().str();
			  toFuns.push_back(funName);
			}
		}
	  
	  // Getting Top-level node
	  FPkind topKind = NoInfo;
	  PAGNode* topNode = getTopNode(fpNode);	  
	  std::string topName = topNode->getValue()->getName().str();
	  NodeKind topNodeKind = checkNodeKind(topNode);

	  // For conditional expression
	  // Case of (cond ? F : G)() --> skip
	  // Case of (cond ? fp : G)() --> skip (out of assumption)		  
	  const llvm::SelectInst* sel = dyn_cast<SelectInst>(fpNode->getValue());
	  const llvm::PHINode* phi = dyn_cast<PHINode>(fpNode->getValue());
	  if (sel != NULL || phi != NULL){ topNodeKind = UNKNOWN; goto Output; }

	  // For FPVAR/FPARR cases, goto Output directly since it's already finished	  
	  if (topNodeKind == FPVAR) { topKind = Var; goto Output; }
	  if (topNodeKind == FPARR) { topKind = Arr; goto Output; }		

	  // For FPFLD case
	  topKind = getTopFpKind(topNode);

	  // Creating field info
	  createFlds(fpNode,topNode,&flds);
	  std::reverse(flds.begin(),flds.end());	 
	
	Output:
	  jsonResult.push_back( mkJSON(topName,topKind,flds,inFun,toFuns) );
	}

  std::string jsonOutput = "[\n" + stringVector(jsonResult,_None,_None,_CommaNewLine,_NewLine) + "]\n";  
  cout << jsonOutput;
  
  return 0;
}

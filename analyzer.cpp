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

// For Debugging 
int debugflag = false;

std::string _Quote = "\"";
std::string _Comma = ", ";
std::string _None = "";
std::string _NewLine = "\n";
std::string _CommaNewLine = ",\n";

std::string addQuote(const std::string str){
  return "\"" + str + "\"";
}


// To display elements
std::string getTypeName(const llvm::Type* tp)
{
  if (tp == NULL) { return("NullType"); }
  std::string str;
  raw_string_ostream rawstr(str);
  tp->print(rawstr);
  return (rawstr.str());
}

void peekType(const llvm::Type* tp)
{
  cout << getTypeName(tp) << "\n" << flush;
  return;  
}

void peekValue(const llvm::Value *val)
{
  if (val == NULL){ cout << "It's NULL!\n"; return; }
  std::string str;
  raw_string_ostream rawstr(str);
  val->print(rawstr);
  cout << rawstr.str() << "\n" << flush;
  return;
}

void peekNode(PAGNode* node)
{
  if (node == NULL) { cout << "NullNode!\n"; return; }
  const llvm::Value* val = node->getValue();
  peekValue(val);
  return;
}

void debugPeekNode(std::string mes, PAGNode* node)
{
  if (!debugflag) return;
  cout << mes; peekNode(node);
  return;
}

void debugPeekValue(std::string mes, const llvm::Value* val)
{
  if (!debugflag) return;
  cout << mes; peekValue(val);
  return;
}

void debugPeekType(std::string mes, const llvm::Type* tp)
{
  if (!debugflag) return;
  cout << mes; peekType(tp);
  return;
}

void debugPeekString(std::string mes1, std::string mes2)
{
  if (!debugflag) return;
  cout << mes1 << mes2 << "\n";
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
  debugPeekString("mkJSON-Begin", "");
  debugPeekString("mkJSON: name: ", name);  
  debugPeekString("mkJSON: kind: ", kind2str(kind));
  
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
	  debugPeekString("mkJSON-End: ", "FPVAR");	  
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
	  debugPeekString("mkJSON-End: ", "FPARR");	  
	  return (rawstr.str());
	}

  // put tagFPFLD here
  // FPFLD case
  rawstr << "[" + tagFPFLD + comma + "{";
  rawstr << keyPtr + colon + addQuote(name);
  rawstr << comma;
  //  rawstr << keyKind + colon + addQuote(kind2str(kind));
  //  rawstr << comma;  
  rawstr << keyFld + colon + "[" << stringVector(flds,_None,_None,_Comma,_None) << "]";
  rawstr << comma;  
  rawstr << keyInFun + colon + addQuote(inFun);
  rawstr << comma;
  rawstr << keyToFuns + colon + "[" << stringVector(toFuns,_Quote,_Quote,_Comma,_None) << "] ";
  rawstr << "}]";
  debugPeekString("mkJSON-End: ", "FPFLD");  
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
	  if(opCodeName == "bitcast") return("BITCAST");	  
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
  if(node == NULL) { cout << "getParentNode: NULL node\n"; return(NULL); }
  PAGEdge::PAGEdgeSetTy::iterator edge = node->getIncomingEdges(edgeKind).begin();
  if(*edge == NULL) return(NULL);
  return (*edge)->getSrcNode();
}				   


// Getting the distination node of a LOAD edge from 'node'
// If 'node' doesn't have a LOAD edge, this returns NULL
std::vector<PAGNode*> getLoadDist(PAGNode* node)
{
  if(node == NULL) { cout << "getParentNode: NULL node\n"; exit(1); }
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
  return (getLoadDist(node).size() != 0);
}

// Get the TopNode (start node for obtaining fpcall info) of given node
// TopNode is ALLOCA for local variables, COMMON for global variables
PAGNode* getTopNode(PAGNode* node)
{
  debugPeekNode("getTopNode-Begin: ", node);
  PAGEdge::PAGEdgeSetTy::iterator edge1,edge2,edge3,edge;  
  PAGNode* nd = node;

  while (nd != NULL)
	{
	  debugPeekNode("getTopNode (in loop): ", nd);
	  //	  fprintf(stderr,"getTopNodeBegin-%d\n",ctr);
	  edge1 = nd->getIncomingEdges(PAGEdge::NormalGep).begin();
	  edge2 = nd->getIncomingEdges(PAGEdge::Load).begin();
	  edge3 = nd->getIncomingEdges(PAGEdge::Copy).begin();	// for union
											  
	  /*
	  PAGEdge::PAGEdgeSetTy::iterator edge4 = nd->getIncomingEdges(PAGEdge::Store).begin();
	  PAGEdge::PAGEdgeSetTy::iterator edge5 = nd->getIncomingEdges(PAGEdge::Call).begin();
	  PAGEdge::PAGEdgeSetTy::iterator edge6 = nd->getIncomingEdges(PAGEdge::Ret).begin();
	  PAGEdge::PAGEdgeSetTy::iterator edge7 = nd->getIncomingEdges(PAGEdge::VariantGep).begin();
	  PAGEdge::PAGEdgeSetTy::iterator edge8 = nd->getIncomingEdges(PAGEdge::ThreadFork).begin();
	  PAGEdge::PAGEdgeSetTy::iterator edge9 = nd->getIncomingEdges(PAGEdge::ThreadJoin).begin();
	  PAGEdge::PAGEdgeSetTy::iterator edge10 = nd->getIncomingEdges(PAGEdge::Addr).begin();	  
	  if (checkNodeType(nd) == "ALLOCA" || checkNodeType(nd) == "GLOBAL") break;
	  if (*edge3 != NULL) { cout << "Copy is found!\n"; break; }
	  if (*edge4 != NULL) { cout << "Store is found!\n"; break; }	  
	  if (*edge5 != NULL) { cout << "Call is found!\n"; break; }
	  if (*edge6 != NULL) { cout << "Ret is found!\n"; break; }
	  if (*edge7 != NULL) { cout << "VariantGep is found!\n"; break; }
	  if (*edge8 != NULL) { cout << "ThreadFork is found!\n"; break; }
	  if (*edge9 != NULL) { cout << "ThreadJoin is found!\n"; break; }
	  if (*edge10 != NULL) { cout << "Addr is found!\n"; break; }
	  */	  
	  if (*edge1 == NULL && *edge2 == NULL && *edge3 == NULL) break;
	  if (*edge1 != NULL) edge = edge1;
	  else
		if (*edge2 != NULL) edge = edge2;
		else
		  if (*edge3 != NULL
			  && (checkNodeType((*edge3)->getSrcNode()) == "ALLOCA" || checkNodeType((*edge3)->getSrcNode()) == "GEP"))
			  edge = edge3;
		  else break;
	  nd = (*edge)->getSrcNode();
	  //	  fprintf(stderr,"getTopNodeEnd-%d\n",ctr);
	}
  debugPeekNode("getTopNode-End: ", nd);  
  return(nd);
}


typedef enum { UNKNOWN, VAR, ARR, STRUCT, UNION } NodeKind;

// This is used only for top-node (alloca node)
NodeKind checkNodeKind(PAGNode* node)
{
  if (node == NULL) return (UNKNOWN);
  SVF::PAGEdge::PAGEdgeSetTy loadEdgeItr = node->getOutgoingEdges(PAGEdge::Load);
  SVF::PAGEdge::PAGEdgeSetTy  gepEdgeItr = node->getOutgoingEdges(PAGEdge::NormalGep);
  SVF::PAGEdge::PAGEdgeSetTy  copyEdgeItr = node->getOutgoingEdges(PAGEdge::Copy);

  if (copyEdgeItr.size() != 0) return(UNION);

  if (loadEdgeItr.size() != 0)
	{
	  std::vector<PAGNode*> nodes = getLoadDist(node);
	  if (nodes[0] == NULL) { return(UNKNOWN); }
	  if (nodes[0]->getOutgoingEdges(PAGEdge::NormalGep).size() == 0
		  && nodes[0]->getOutgoingEdges(PAGEdge::Copy).size() == 0) return (VAR);
	  else return (STRUCT);
	}

  for (auto iter = gepEdgeItr.begin(), iend = gepEdgeItr.end(); iter != iend; iter++)
	{
	  PAGNode* nd = (*iter)->getDstNode();
	  if(nd == NULL) { return (UNKNOWN); }
	  std::string name = nd->getValue()->getName().str();
	  if (name.find("arrayidx") != std::string::npos
		  && getLoadDist(nd).size() > 0
		  && getLoadDist(nd)[0]->getOutgoingEdges(PAGEdge::NormalGep).size() == 0)
		return (ARR);
	}
  
  return (STRUCT);
}

std::string nodekind2str(NodeKind nk)
{
  switch(nk)
	{
	case UNKNOWN: return "UNKNOWN";
	case VAR:     return "VAR";
	case ARR:     return "ARR";
	case STRUCT:  return "STRUCT";
	case UNION:  return "UNION";	  
	}
  return "";
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
	  if (nd == NULL) { continue; }
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
  debugPeekNode("getPrevPointer-Begin: node: ", node);
  if (node == NULL) { cout << "getPrePointer:NULL-input\n"; return ("dummy"); }
  const llvm::Value* val = node->getValue();
  const llvm::GetElementPtrInst* gepInst = dyn_cast<GetElementPtrInst>(val);
  const llvm::LoadInst* loadInst = dyn_cast<LoadInst>(val);
  const llvm::CastInst*	castInst = dyn_cast<CastInst>(val);
  
  debugPeekValue("getPrevPointer-2: ", val);  
  std::string ptr = "dummy";
  if(loadInst != NULL){
	ptr = loadInst->getPointerOperand()->getName().str();
  }
  else
	if(gepInst != NULL){
	  ptr = gepInst->getPointerOperand()->getName().str();
	} else
	  if (castInst != NULL){
		llvm::Type* tp = castInst->getSrcTy();
		if (!tp->isPointerTy ()){ cout << "Unexpected type\n"; exit(1); }
		ptr = val->stripPointerCasts()->getName().str();
	  }
  debugPeekString("getPrePointer-End: ", ptr); 
  return(ptr);
}


typedef struct NK {
  PAGNode* node;
  FPkind kind;
} NK;

// Finding a next gep node
// bottom-up creating of a field info
NK* nextGep(NK* nodekind, PAGNode* topNode)
{
  debugPeekNode("nextGep-Begin: nodekind->node: ", nodekind->node);
  if(topNode == NULL || topNode->getValue() == NULL){
	cout << "nextGep: Unexpected topNode\n"; exit(1);
  }
  if(nodekind->node == NULL || nodekind->node->getValue() == NULL){
	cout << "nextGep: Unexpected curNode\n"; exit(1);
  }  
  std::string topName = topNode->getValue()->getName().str();  
  std::string subgoal = nodekind->node->getValue()->getName().str();  
  bool ptrFlag = false;
  bool arrFlag = false;
  debugPeekString("nextGep-1: subgoal(init): ", subgoal); // initial subgoal is the current node
  debugPeekString("nextGep-1: topName: ", topName);    
  debugPeekNode("nextGep-1:nodekind->node: ", nodekind->node);  
  
  while(true) // curNode is a gep-node or a load-node && subgoal = curName
	{
	  if(nodekind->node == NULL || nodekind->node->getValue() == NULL){
		cout << "nextGep: Unexpected nodekind (in while)\n";
		exit(1);
	  }
	  debugPeekNode("nextGep-2:nodekind->node: ", nodekind->node);
	  subgoal = getPrevPointer(nodekind->node);
	  debugPeekNode("nextGep-3:nodekind->node: ", nodekind->node);
	  debugPeekString("nextGep-3:topName: ", topName);
	  debugPeekString("nextGep-3:subgoal: ", subgoal);
	  if(subgoal.find("arrayidx") != std::string::npos) { arrFlag = true; }
	  if(subgoal == topName) {
		nodekind->node = NULL;
		nodekind->kind = NoInfo;
		debugPeekNode("nextGep-End:Reached topNode:", topNode);
		return(nodekind);
	  }
	  debugPeekNode("nextGep-4:nodekind->node: ", nodekind->node);
	  if(dyn_cast<LoadInst>(nodekind->node->getValue()) != NULL)
		{
		  nodekind->node = getParentNode(nodekind->node, PAGEdge::Load);
		  ptrFlag = true;
		  break;
		}
	  debugPeekNode("nextGep-5:nodekind->node: ", nodekind->node);
	  PAGNode* node1 = getParentNode(nodekind->node, PAGEdge::NormalGep);
	  PAGNode* node2 = getParentNode(nodekind->node, PAGEdge::Copy); // for the case: alloca -COPY-> bitcast %union
	  nodekind->node = (node1 != NULL) ? node1 : node2;
	  debugPeekNode("nextGep-6:nodekind->node: ", nodekind->node);
	  debugPeekString("nextGep-6:subgoal: ", subgoal);
	  debugPeekValue("nextGep-6:nodekind->node->getValue(): ", nodekind->node->getValue());
	  std::string curName = nodekind->node->getValue()->getName().str();
	  debugPeekNode("nextGep-7:nodekind->node: ", nodekind->node);
	  if(curName == subgoal){
		if (subgoal == "") continue;
		debugPeekString("nextGep-7: reached subgoal: ",subgoal);
		break;
	  }	  
	  PAGEdge::PAGEdgeSetTy edgeItr = nodekind->node->getOutgoingEdges(PAGEdge::NormalGep);
	  debugPeekNode("nextGep-8:nodekind->node: ", nodekind->node);
	  for (auto edge = edgeItr.begin(), iend = edgeItr.end(); edge != iend; edge++)
		{
		  if(*edge == NULL) { cout << "Something unexpected happens!"; exit(1); }
		  PAGNode* dst = (*edge)->getDstNode();
		  debugPeekNode("nextGep-9:nodekind->node: ", nodekind->node);
		  if(subgoal == dst->getValue()->getName().str())
			{
			  nodekind->node = dst;
			  break;
			}
		  debugPeekNode("nextGep-A:nodekind->node: ", nodekind->node);
		}
	  debugPeekNode("nextGep-B:nodekind->node: ", nodekind->node);
	  if(subgoal.find("arrayidx") == std::string::npos) break;
	}
  nodekind->kind = ptrFlag ? (arrFlag ? ArrPtr : Ptr) : (arrFlag ? Arr : Var);
  debugPeekNode("nextGep-End: nodekind->node: ", nodekind->node);
  return(nodekind);
}

std::string createFldOne(NK* nodekind)
{
  // making fld_index
  debugPeekNode("createFldOne-Begin:nodekind->node: ", nodekind->node);
  std::string  fldIndex = "0";
  std::string  strTpName = "NoType";
  const llvm::Value* val = nodekind->node->getValue();
  const llvm::Instruction* inst = dyn_cast<Instruction>(val);
  llvm::Type* tp = NULL;
  
  debugPeekValue("createFldOne-0:nodekind->node->getValue(): ", val);
  const llvm::GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(inst);
  if(gep != NULL)
	{ // normal case 
	  std::string fld;
	  raw_string_ostream rawstr(fld);
	  auto fldPosValueItr = gep->idx_begin();
	  fldPosValueItr++;
	  if ((*fldPosValueItr) == NULL) { cout << "createFldOne: Unexpected fldPosValue\n"; return(""); }  
	  (*fldPosValueItr)->print(rawstr); // field position, like "i32 5" (5-th pos)
	  fldIndex = rawstr.str().substr(4); // "i32 5" --> "5"
	  debugPeekNode("createFldOne-1:nodekind->node: ", nodekind->node);
  
	  // making fld_name
	  if(nodekind->node == NULL) { cout << "createFldOne: Unexpected node\n"; return(""); }  

	  // making tp
	  tp = gep->getSourceElementType();
	  debugPeekType("createFldOne-2a:gep->getSourceElementType(): ", tp);
	  if (tp->isStructTy())
		{
		  strTpName = dyn_cast<StructType>(tp)->getName().str();
		  debugPeekString("createFldOne-2a:strTpName: ",strTpName);
		}
	  else
		if (tp->isArrayTy())
			return(""); // just skip 
		else
		  {
			cout << "createFldOne: unexpected type-1\n";
			exit(1);
		  }
	}
  else
	if (inst->isCast())
	{ // nodekind->node is bitcast (union case)
	  tp = dyn_cast<CastInst>(inst)->getSrcTy();
	  debugPeekType("createFldOne-2b:dyn_cast<CastInst>(inst)->getSrcTy(): ", tp);
	  strTpName = getTypeName(tp);
	  debugPeekString("createFldOne-2b:strTpName: ",strTpName);
	}
	else
	  {
		cout << "Error: createFldOne: the following node is not bitcast\n";
		peekValue(val);
		exit(1);
	  }
  debugPeekNode("createFldOne-3:nodekind->node: ", nodekind->node);
  debugPeekValue("createFldOne-3:nodekind->node->getValue(): ", nodekind->node->getValue());
  std::string fldName = nodekind->node->getValue()->getName().str();
  std::string fldOne = "{"
	+ keyTp + colon + addQuote(strTpName) 
	+ "," + keyFldName + colon + addQuote(fldName) 
	+ "," + keyFldIndex + colon + fldIndex
	//	+ "," + keyKind + colon + addQuote(kind2str(nodekind->kind))
	+ "}";
  debugPeekString("createFldOne-End:nodekind->node: ", fldOne);    
  return (fldOne);
}


// Creating Fields (main part)
void createFlds(PAGNode* fpNode, PAGNode* topNode, std::vector<string>* fldsP)
{
  debugPeekString("createFlds-Begin", "");  
  NK* nodekind = (NK*)malloc(sizeof(NK));
  nodekind->node = getParentNode(fpNode,PAGEdge::Load); // GEP node or bitcast node
  nodekind->kind = Ptr; // initial fp should be a pointer
  debugPeekNode("createFlds-0:nodekind->node: ", nodekind->node);
  debugPeekNode("createFlds-0:fpNode        : ", fpNode);
  debugPeekNode("createFlds-0:topNode       : ", topNode);
  std::string fld = createFldOne(nodekind);
  if(fldsP == NULL) { cout << "createFlds: unexpected fldsP\n" ; free(nodekind); return; }
  //  if(fld != "" && checkNodeType(nodekind->node) == "GEP"){
  if(fld != ""
	 && fld.find("arrayidx") == std::string::npos
	 && fld.find("{}") == std::string::npos
	 ) // Do not push if array field or meaningless type comes
	{
	  debugPeekString("createFlds-0: push: ",fld);
	  (*fldsP).push_back(fld); 
	}

  while(true)
	{
	  debugPeekNode("createFlds (in loop): nodekind->node: ", nodekind->node);	  
	  nodekind = nextGep(nodekind,topNode);
	  debugPeekNode("createFlds (in loop): nodekind->node: ", nodekind->node);	  
	  if(nodekind->node == NULL) {
		break; // when no nextGep
	  }
	  debugPeekString("createFlds (in loop): before createFldOne", "");
	  std::string fld1 = createFldOne(nodekind);
	  debugPeekString("createFlds-3 (in loop): after  createFldOne", "");
	  if(fld1 != ""
		 && fld1.find("arrayidx") == std::string::npos
		 && fld1.find("{}") == std::string::npos
		 ) // Do not push if array field or meaningless type comes
		{
		  debugPeekString("createFlds (in loop): push: ",fld1);
		  (*fldsP).push_back(fld1);
		}
	}
  free (nodekind);
  debugPeekString("createFlds-End", "");  
  return;
}


std::string mkJsonOneCall(NodeID fpNodeID, PAG* pag, Andersen * ander)
{
  std::string res;
  raw_string_ostream rawstr(res);
  std::vector<std::string> flds;
  
  // function pointer load node for fpcall, like %20 = load %fp2
  PAGNode* fpNode = pag->getPAGNode(fpNodeID);

  debugPeekString("---------------------","");
  debugPeekNode ("mkJsonOneCall Begin: ", fpNode);
  debugPeekString("--------","");
  
  // Making in-fun
  string inFun = (fpNode != NULL && fpNode->getFunction() != NULL) ? fpNode->getFunction()->getName().str() : "FAILED-TO-GET_INFUN";
	  
  // Getting function values for fpNode from the SVF analysis result
  const NodeBS& fpPts = ander->getPts(fpNodeID); // iterator	  
  PAGNode* fpPagNode = ander->getPAG()->getPAGNode(*fpPts.begin());

  // Checking: Skip if the tail-part contains a non-function node	  
  if( !fpPagNode->hasValue() )
	{
	  // debugPeekString("mkJsonOneCall: ","fpcall with no Value! (fail)");
	  cout << "mkJsonOneCall: fpcall with no Value! (fail)";
	  exit(1);
	}
  // Checking: Skip if the tail-part contains a non-function node	  
  if (fpPagNode == NULL
	  || fpPagNode->getType() == NULL
	  || fpPagNode->getType()->getTypeID() != llvm::Type::FunctionTyID)
	return("continue");

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
  if(topNode == NULL) { cout << "No TopNode\n"; exit(1); }
  std::string topName = topNode->getValue()->getName().str();
  NodeKind topNodeKind = checkNodeKind(topNode);
  debugPeekNode("mkJsonOneCall: topNode: ", topNode);
  debugPeekString("mkJsonOneCall: topKind: ", kind2str(topKind));
  debugPeekString("mkJsonOneCall: topNodeKind: ", nodekind2str(topNodeKind));

  // For conditional expression
  // Case of (cond ? F : G)() --> skip
  // Case of (cond ? fp : G)() --> skip (out of assumption)		  
  const llvm::SelectInst* sel = dyn_cast<SelectInst>(topNode->getValue());
  const llvm::PHINode* phi = dyn_cast<PHINode>(topNode->getValue());
  if (sel != NULL || phi != NULL){
	topNodeKind = UNKNOWN;
	return "continue";
  }

  // For VAR/ARR cases, goto Output directly since it's already finished	  
  if (topNodeKind == VAR) {
	debugPeekString("mkJsonOneCall: topNodeKind: ", "VAR");
	topKind = Var;
	goto Output;
  }
  if (topNodeKind == ARR) {
	debugPeekString("mkJsonOneCall: topNodeKind: ", "ARR");
	topKind = Arr;
	goto Output;
  }

  // For STRUCT/UNION case
  topKind = getTopFpKind(topNode);

  // Creating field info
  //  cout << "fpNode (main): "; peekNode(fpNode);
  createFlds(fpNode,topNode,&flds);
  std::reverse(flds.begin(),flds.end());  
  
 Output:
  std::string jsonStr = mkJSON(topName,topKind,flds,inFun,toFuns);
  debugPeekString ("mkJsonOneCall End: ", jsonStr);
  debugPeekString ("","");
  return(jsonStr);
}


int main(int argc, char ** argv)
{
  debugPeekString("Main starts","");
  // argment processing for SVF
  int arg_num = 0;
  char** arg_value = new char*[argc];
  std::vector<std::string> moduleNameVec;
  SVFUtil::processArguments(argc, argv, arg_num, arg_value, moduleNameVec);
  SVFModule* svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(moduleNameVec);
  
  /// Build Program Assignment Graph (PAG)
  PAGBuilder builder;
  PAG* pag = builder.build(svfModule);

  /// Create Andersen's pointer analysis
  Andersen *ander = AndersenWaveDiff::createAndersenWaveDiff(pag);

  const PAG::CallSiteToFunPtrMap& aaa = pag->getIndirectCallsites();
  std::vector<std::string> jsonResult;

  for (auto iter = aaa.begin(), iend = aaa.end(); iter != iend; iter++)
	{
	  NodeID fpNodeID = (*iter).second;
	  std::string s = mkJsonOneCall(fpNodeID, pag, ander);
	  if(s != "continue") jsonResult.push_back(s);
	}
  
  std::string jsonOutput = "[\n" + stringVector(jsonResult,_None,_None,_CommaNewLine,_NewLine) + "]\n";  
  cout << jsonOutput;

  delete ander;
  delete pag;    
  delete svfModule;  
  return 0;
}

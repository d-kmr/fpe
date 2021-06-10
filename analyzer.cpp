/*
 // A driver program of SVF including usages of SVF APIs
 */

#include "SVF-FE/LLVMUtil.h"
#include "Graphs/SVFG.h"
#include "WPA/Andersen.h"
#include "SABER/LeakChecker.h"
#include "SVF-FE/PAGBuilder.h"


std::string addQuote(const std::string str){
  return "\"" + str + "\"";
}

std::string tagFPFLD = addQuote("FPFLD");
std::string tagFPVAR = addQuote("FPVAR");
std::string tagFPARR = addQuote("FPARR");
std::string keyName = addQuote("name");
std::string keyTpName = addQuote("tp");
std::string keyFldName = addQuote("fld_name");
std::string keyFldIndex = addQuote("fld_index");
std::string keyInFun = addQuote("in_fun");
std::string keyToFuns = addQuote("to_funs");
std::string keyPtr = addQuote("ptr");
std::string keyFld = addQuote("fld");
std::string colon = ":";
std::string comma = ", ";


using namespace SVF;
using namespace llvm;
using namespace std;

static llvm::cl::opt<std::string> InputFilename(cl::Positional,
        llvm::cl::desc("<input bitcode>"), llvm::cl::init("-"));

static llvm::cl::opt<bool> LEAKCHECKER("leak", llvm::cl::init(false),
                                       llvm::cl::desc("Memory Leak Detection"));

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

void checkIncommingEdge(PAGNode* node){
  // Addr, Copy, Store, Load, Call, Ret, NormalGep, VariantGep, ThreadFork, ThreadJoin, Cmp, BinaryOp, UnaryOp  
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

std::string checkInstruction(const llvm::Instruction *inst){
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

// getParentNode
// If the current struct-field access is a->f->g, and current node is 'g',
// its parent is 'f'
// if there is no parent, NULL is returned
PAGNode* getParentNode(PAGNode* src){
  PAGEdge::PAGEdgeSetTy::iterator edge;
  PAGNode* node;
  edge = src->getIncomingEdges(PAGEdge::NormalGep).begin();
  if(*edge != NULL) {
	node = (*edge)->getSrcNode();
	if(node->getValue()->getName() == ""){
	  edge = node->getIncomingEdges(PAGEdge::Load).begin();
	  if(*edge != NULL){
		node = (*edge)->getSrcNode();
	  }
	}
	return node;
  }
  
  edge = src->getIncomingEdges(PAGEdge::Copy).begin();
  if(*edge != NULL){
	node = (*edge)->getSrcNode();
	if(node->getValue()->getName() == ""){
	  edge = node->getIncomingEdges(PAGEdge::Load).begin();
	  if(*edge != NULL){
		node = (*edge)->getSrcNode();
	  }
	}
	return node;
  }
  return NULL;
}

void peekValue(const llvm::Value *val){
  if (val == NULL){ cout << "It's NULL!\n"; return; }
  std::string str;
  raw_string_ostream rawstr(str);
  val->print(rawstr);
  cout << rawstr.str() << "\n";
  return;
}

bool isCallNode(PAGNode* node){
  if (!node->hasValue()) return false;
  const CallInst* callinst = dyn_cast<CallInst>(node->getValue());
  if (callinst == NULL) return false;
  return true;
}

std::string mkFPcall(PAG* pag, const llvm::Value *val){
  const CallBase* callbase = dyn_cast<CallBase>(val);
  if (callbase == NULL) return "_";

  /* making the function name part */
  std::string funstr = "";
  Function *fun = callbase->getCalledFunction();
  if (fun)
	{ // direct-call
	  funstr = fun->getName();
	}
  else
	{// indirect-call
	  NodeID pNodeId = pag->getValueNode(val);
	  PAGNode* node = pag->getPAGNode(pNodeId);
	  const PAG::CallSiteToFunPtrMap& csmap = pag->getIndirectCallsites();
	  const SVF::CallBlockNode* cs;
	  NodeID fpNodeId;

	  for (auto iter = csmap.begin(), iend = csmap.end(); iter != iend; iter++)
		{
		  cs = (*iter).first;
		  fpNodeId = (*iter).second;
		  // cout << (cs->getActualParms())[0]->getValue() << "\n";
		  // if ((*iter).second == pNodeId) break;
		  // cout << cs->toString() << " --> " << fpNodeId << "\n";		
		}
	}
  
  
  /* making the argment part */
  std::string argstr = "";
  auto ii=callbase->arg_begin(), ie=callbase->arg_end();

  if (ii != ie) { argstr = mkFPcall(pag,*ii); ii++; }
  for (; ii != ie; ii++){
	argstr = argstr + "," + mkFPcall(pag,*ii);
  }
  argstr = "(" + argstr + ")";
  
  return (funstr + argstr);
  
}

std::vector<std::string> getCurrentName(PAG* pag,PAGNode* src){
  // Returns [id,name]
  // ["",""]  --> nothing
  // ["FPFLD",name] --> field case (name = {"fld_name":<fld>,"fld_index":<pos>})
  // ["FPARR",""] --> array case (do not care the index)
  std::vector<std::string> result;
  
  if (src == NULL || !src->hasValue()){
	result.push_back("");
	result.push_back("");
	return result;
  }

  /* Check whether src is a call-node */
  if(isCallNode(src)){
  	std::string fpcall = mkFPcall(pag,src->getValue());
	result.push_back("");
	result.push_back(fpcall);
  	return result;
  }

  std::string name = src->getValue()->getName().str();
  
  const llvm::Value* v = src->getValue();
  const llvm::GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(src->getValue());
  
  if (gep != NULL){
	std::string fld;
	raw_string_ostream rawstr(fld);	  
	
	auto ii=gep->idx_begin();
	ii++;
	llvm::Value* fldPosValue = *ii;
	fldPosValue->print(rawstr); // field position, like "i32 5" (5-th pos)
	std::string fldPos = rawstr.str().substr(4); // "i32 5" --> "5"

	if (name == "" || name.find("arrayidx") != std::string::npos){ // FPARR-case (name == "arrayidx123")
	  name = fldPos;	  
	  result.push_back("FPARR");
	  result.push_back("");
	  return result;
	}
	else { // FPFLD-case
	  /*
	  llvm::Type* tp = gep->getSourceElementType();
	  if (tp->isStructTy()){
		structTypeName = strTp->getName().str();
	  }
	  */
	  llvm::Type* tp = gep->getSourceElementType();
	  std::string strTpName = "";
	  if(tp->isStructTy()){
		strTpName = dyn_cast<StructType>(tp)->getName().str();
	  }
	  
	  name = "{"
		+ keyTpName + colon + addQuote(strTpName) + ","
		+ keyFldName + colon + addQuote(name) + ","
		+ keyFldIndex + colon + fldPos
		+ "}";
	  result.push_back("FPFLD");
	  result.push_back(name);
	  return result;
	}
  }
  
  if (name == ""){
	PAGNode* node = getParentNode(src);
	if (node == NULL) { result.push_back(""); result.push_back(""); return result; }
	name = node->getValue()->getName().str();
  }
  result.push_back("");  
  result.push_back(name);
  return result;
}

// Node0x557e1d09ad30 [shape=record,shape=circle,label="{[main] ValPN ID: 4294967227   %f = getelementptr inbounds %struct.A, %struct.A* %8, i32 0, i32 4 \{  \}}"];

// stringVector: it returns a string of the given string list
// l: the left additional string of each element 
// r: the right additional string of each element
// e.g. aaa -> [aaa], if l and r are [ and ]
// sep: the separation symbol
// last: the lastly added symbol
std::string stringVector(std::vector<std::string> v, std::string l, std::string r, std::string sep, std::string last){
  std::string str;
  raw_string_ostream rawstr(str);
  for (std::vector<std::string>::iterator ii=v.begin(), ie=v.end(); ii != ie; ii++){
	if (ii != v.begin()) rawstr << sep;
	rawstr << l << *ii << r;
  }
  rawstr << last;
  return rawstr.str();
}



int main(int argc, char ** argv) {
  // argment processing for SVF
  int arg_num = 0;
  char **arg_value = new char*[argc];
  std::vector<std::string> moduleNameVec;
  SVFUtil::processArguments(argc, argv, arg_num, arg_value, moduleNameVec);
  SVFModule* svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(moduleNameVec);

  // outputStyle: 0=JSON-style (default), 1=simple-style (when something after .bc filename is given)
  int outputStyle = 0;
  if(argc > 2) outputStyle = 1;

  std::string _quote = "\"", _comma = ", ", _none = "", _newline = "\n",_commanewline = ",\n";
	
  /// Build Program Assignment Graph (PAG)
  PAGBuilder builder;
  PAG *pag = builder.build(svfModule);
  // pag->dump("pag");

  /// Create Andersen's pointer analysis
  Andersen *ander = AndersenWaveDiff::createAndersenWaveDiff(pag);

  const PAG::CallSiteToFunPtrMap& aaa = pag->getIndirectCallsites();
  //	NodeBS::iterator ii,ie;
  NodeID fpNodeID;
  std::string headStr, tailStr;
  PAGNode *fpNode, *refNode;

  std::vector<std::string> result;
	
  for (auto iter = aaa.begin(), iend = aaa.end(); iter != iend; iter++){
	std::vector<std::string> toFuns;
	  
	headStr = "";
	tailStr = "";

	// TAIL-part
	fpNodeID = (*iter).second;
	const NodeBS& tailPts = ander->getPts(fpNodeID); // iterator	  
	// Check: Skip if the tail-part contains a non-function node
	refNode = ander->getPAG()->getPAGNode(*tailPts.begin());
	if (refNode == NULL
		|| !refNode->hasValue()
		|| refNode->getType() == NULL
		|| refNode->getType()->getTypeID() != llvm::Type::FunctionTyID)
	  continue;
	// Create the tail-part
	for (NodeBS::iterator ii=tailPts.begin(), ie=tailPts.end() ; ii != ie; ++ii) {
	  refNode = ander->getPAG()->getPAGNode(*ii);
	  if(refNode->hasValue()){
		const std::string funName = refNode->getValue()->getName().str();
		toFuns.push_back(funName);
	  }
	}
	
	// fpKind: 0=FPVAR, 1=FPFLD, 2=FPARR, -1=Skip
	int fpKind = 0;

	// Result
	std::string res;
	raw_string_ostream rawstr(res);
	
	// HEAD-part
	std::vector<std::string> head, flds, getCurrentNameResult;
	std::string inFun;
	std::string hdName;
	
	fpNode = pag->getPAGNode(fpNodeID);

	// Case of (cond ? F : G)() --> skip
	// Case of (cond ? fp : G)() --> skip (out of assumption)	
	const llvm::SelectInst* sel = dyn_cast<SelectInst>(fpNode->getValue());
	const llvm::PHINode* phi = dyn_cast<PHINode>(fpNode->getValue());	
	if (sel != NULL || phi != NULL){ fpKind = -1; goto Output; }
	
	if (fpNode != NULL && fpNode->getFunction() != NULL){
	  inFun = fpNode->getFunction()->getName(); // get parent func.name in which "%0" appears
	} else {
	  inFun = "";
	}
	  
	// update by the source of the incoming Load edge (if exists)
	if (fpNode->hasIncomingEdges(PAGEdge::Load)){
	  PAGEdge::PAGEdgeSetTy::iterator edge = fpNode->getIncomingEdges(PAGEdge::Load).begin();
	  fpNode = (*edge)->getSrcNode();
	}

	getCurrentNameResult = getCurrentName(pag,fpNode); // ["",""] or ["FPFLD",<flds>] or ["FPARR",<index>]
	if (getCurrentNameResult[0] == "FPFLD") fpKind = 1; 	// FPFLD-case  
	if (getCurrentNameResult[0] == "FPARR") fpKind = 2; 	// FPARR-case
	
	//	if (head.size() > 1) fpKind = 1; 	// FPFLD-case
		
	head.push_back(getCurrentName(pag,fpNode)[1]);
	fpNode = getParentNode(fpNode);
	while(fpNode != NULL){
	  //head.push_back(fpNode->getValue()->getName().str());
	  head.push_back(getCurrentName(pag,fpNode)[1]);
	  fpNode = getParentNode(fpNode);
	}

	hdName = head[head.size()-1];
	for(int i = 0; i < head.size()-1; i++){
	  flds.push_back(head[head.size()-i-2]);
	}
	
  Output:
	switch(outputStyle){
	case 0: // JSON-style output
	  switch (fpKind){
	  case 0: // FPVAR-case
		rawstr << "[" + tagFPVAR + comma + "{";		
		rawstr << keyName + colon + addQuote(hdName);
		rawstr << comma;
		rawstr << keyInFun + colon + addQuote(inFun);
		rawstr << comma;
		rawstr << keyToFuns + colon + "[" << stringVector(toFuns,_quote,_quote,_comma,_none) << "] ";
		rawstr << "}]";
		result.push_back(rawstr.str());		
		break;
	  case 1: // FPFLD-case
		rawstr << "[" + tagFPFLD + comma + "{";
		rawstr << keyPtr + colon + addQuote(hdName) + comma;
		rawstr << keyFld + colon + "[" << stringVector(flds,_none,_none,_comma,_none) << "]" + comma;		
		rawstr << keyInFun + colon + "\"" << inFun << "\"";
		rawstr << comma;		
		rawstr << keyToFuns + colon + "[" << stringVector(toFuns,_quote,_quote,_comma,_none) << "] ";
		rawstr << "}]";
		result.push_back(rawstr.str());		
		break;
	  case 2: // FPARR-case
		rawstr << "[" + tagFPARR + comma + "{";
		rawstr << keyPtr + colon + addQuote(hdName) + comma;
		//		rawstr << keyIdx + colon << stringVector(flds,_none,_none,_comma,_none) << comma;
		rawstr << keyInFun + colon + "\"" << inFun << "\"";
		rawstr << comma;		
		rawstr << keyToFuns + colon + "[" << stringVector(toFuns,_quote,_quote,_comma,_none) << "] ";
		rawstr << "}]";
		result.push_back(rawstr.str());		
		break;		
	  default: // Skip-case
		break;
	  }
	  break;
	default: // simple output
	  switch (fpKind){
	  case 0: // FPVAR-case
		rawstr << hdName << " @" << inFun << " --> ";
		rawstr << "{" << stringVector(toFuns,_none,_none,_comma,_none) << "}";
		result.push_back(rawstr.str());		
		break;
	  case 1: // FPFLD-case
		rawstr << hdName << "->" << stringVector(flds,_none,_none,"->",_none) << " --> ";
		rawstr << "{" << stringVector(toFuns,_none,_none,_comma,_none) << "}";
		result.push_back(rawstr.str());
		break;
	  default: // Skip-case
		break;
	  }
	  break;
	}
  }

  switch(outputStyle){
  case 0: // JSON-style output
	cout << "[\n" << stringVector(result,_none,_none,_commanewline,_newline) << "]\n";
	break;
  default: // simple-output
	cout << stringVector(result,_none,_none,_newline,_newline);
	break;
  }
	
  return 0;
}

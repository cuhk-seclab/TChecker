package tools.php.ast2cpg;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.Stack;

import ast.ASTNode;
import ast.expressions.ArgumentList;
import ast.expressions.ArrayIndexing;
import ast.expressions.AssignmentExpression;
import ast.expressions.CallExpressionBase;
import ast.expressions.Expression;
import ast.expressions.PropertyExpression;
import ast.expressions.Variable;
import ast.functionDef.ParameterBase;
import ast.functionDef.ParameterList;
import ast.php.expressions.IncludeOrEvalExpression;
import ast.php.functionDef.FunctionDef;
import ast.php.functionDef.Parameter;
import ast.php.functionDef.TopLevelFunctionDef;
import ast.statements.jump.ReturnStatement;
import cg.PHPCGFactory;
import cg.ParseVar;
import ddg.DataDependenceGraph.DDG;
import inputModules.csv.csv2ast.ASTUnderConstruction;
import misc.MultiHashMap;
import misc.Pair;
import outputModules.csv.exporters.CSVCFGExporter;

public class StaticAnalysis  {
	public static Set<Long> sources = PHPCSVEdgeInterpreter.sources;
	public static Set<Long> sinks = new HashSet<Long>();
	public static Set<Long> sqlSanitizers = new HashSet<Long>();
	public static Set<Long> cfgNode = new HashSet<Long>();
	public static MultiHashMap<Long, Long> srcDim = new MultiHashMap<Long, Long>();
	public static MultiHashMap<Long, Long> srcProp = new MultiHashMap<Long, Long>();
	public static MultiHashMap<Long, Long> srcGlobal = new MultiHashMap<Long, Long>();
	public static MultiHashMap<Long, Long> dstGlobal = new MultiHashMap<Long, Long>();
	public static HashMap<Long, Node> ID2Node = new HashMap<Long, Node>();
	public static MultiHashMap<Long, Long> dstProp = new MultiHashMap<Long, Long>();
	public static Node root = new Node((long) 0, new HashMap<String, Long>(), new HashSet<Long>(), new Stack<Long>());
	public static HashSet<Long> vulStmts = new HashSet<Long>();
	public static Set<Stack<Long>> vulPaths = new HashSet<Stack<Long>>();
	public static Long ID = null;
	public static MultiHashMap<String, Long> name2Stmt = new MultiHashMap<String, Long>();
	//we only step into the function 
	public static MultiHashMap<String, Long> name2Func = new MultiHashMap<String, Long>();
	public static MultiHashMap<Long, Long> caller2callee = new MultiHashMap<Long, Long>();
	public static MultiHashMap<Long, Long> callee2caller = new MultiHashMap<Long, Long>();
	public static HashSet<Long> validFunc = new HashSet<Long>();
	//public static MultiHashMap<Long, Node> summary = new MultiHashMap<Long, Node>();
	public static HashMap<Long, Integer> Edgetimes = new HashMap<Long, Integer>();
	public static HashMap<Long, Integer> Edgesize = new HashMap<Long, Integer>();
	
	
	public StaticAnalysis() {
		init();
		for(Long entry: PHPCGFactory.topFunIds) {
			ID2Node = new HashMap<Long, Node>();
			//the source can only be in the main application
			if(PHPCGFactory.getDir(entry).contains("vendor") ||
					PHPCGFactory.getDir(entry).contains("Test")) {
				continue;
			}
			//the file is included/required, so it is not the entry
			if(PHPCGFactory.call2mtd.containsKey(entry)) {
				continue;
			}
			Long stmt = CSVCFGExporter.cfgSave.get(entry+1).get(0);
			Set<Long> intro = new HashSet<Long>();
			ID = (long) 0;
			HashMap<String, Long> inter = new HashMap<String, Long>();
			Stack<Long> callStack = new Stack<Long>();
			Node node = new Node(stmt, inter, intro, callStack);
			constructTaintTree(node);
		}
	}
	
	void init() {
		//collect cfg node
		cfgNode.addAll(CSVCFGExporter.cfgSave.keySet());
		//set the sanitizer statement
		for(Long astID: PHPCSVEdgeInterpreter.sqlSanitizers) {
			Long stmt = getStatement(astID);
			sqlSanitizers.add(stmt);
		}
		//statement -> source dim
		Set<Long> srcGlobalSet = new HashSet<Long>();
		for(Long dim: PHPCSVEdgeInterpreter.dimVar) {
			Long tmp=null, tmp1=null;
			//get the statement of expression
			Long stmt = getStatement(dim);
			ASTNode stmtNode = ASTUnderConstruction.idToNode.get(stmt);
			//it is in assignment
			if(stmtNode instanceof AssignmentExpression) {
				Long rightHandId = ((AssignmentExpression) stmtNode).getRight().getNodeId();
				Long leftHandId = ((AssignmentExpression) stmtNode).getLeft().getNodeId();
				//the dim is in the right hand
				if(rightHandId<=dim) {
					tmp=dim;
				}
				//the dim is assigned
				else if(leftHandId.equals(dim)){
					tmp1=dim;
				}
			}
			//it is a function call
			else if(stmtNode instanceof CallExpressionBase) {
				tmp=dim;
			}
			//the dim is used as source variable
			if(tmp!=null) {
				//the dim is $GLOABLS[] variable
				ASTNode arrayName = ASTUnderConstruction.idToNode.get(dim+2);
				if(arrayName.getProperty("type").equals("string") && arrayName.getEscapedCodeStr().equals("GLOBALS")) {
					srcGlobal.add(stmt, tmp);
					srcGlobalSet.add(tmp);
					Long funcID = stmtNode.getFuncId();
					String iden = getDIMIdentity(ASTUnderConstruction.idToNode.get(dim));
					name2Func(iden, funcID);
				}
				else {
					srcDim.add(stmt, tmp);
				}
			}
			if(tmp1!=null) {
				//the dim is $GLOABLS[] variable
				ASTNode arrayName = ASTUnderConstruction.idToNode.get(dim+2);
				if(arrayName.getProperty("type").equals("string") && arrayName.getEscapedCodeStr().equals("GLOBALS")) {
					dstGlobal.add(stmt, tmp1);
					Long funcID = stmtNode.getFuncId();
					String iden = getDIMIdentity(ASTUnderConstruction.idToNode.get(dim));
					name2Func(iden, funcID);
				}
			}
		}
		//statement -> source property
		Set<Long> srcPropSet = new HashSet<Long>();
		for(Long prop: PHPCSVEdgeInterpreter.property) {
			Long stmt = getStatement(prop);
			ASTNode stmtNode = ASTUnderConstruction.idToNode.get(stmt);
			try {
				//it is in assignment
				if(stmtNode instanceof AssignmentExpression) {
					Long rightHandId = ((AssignmentExpression) stmtNode).getRight().getNodeId();
					Long leftHandId = ((AssignmentExpression) stmtNode).getLeft().getNodeId();
					//it is in the right hand
					if(rightHandId<=prop) {
						srcProp.add(stmt, prop);
						srcPropSet.add(prop);
					}
					//it is in the left hand
					else if(leftHandId.equals(prop)){
						dstProp.add(stmt, prop);
					}
					//get the function of prop
					Long funcID = stmtNode.getFuncId();
					String iden = getPropIdentity(ASTUnderConstruction.idToNode.get(prop), (long) 0);
					name2Func(iden, funcID);
				}
				//it is a function call
				else if(stmtNode instanceof CallExpressionBase) {
					srcProp.add(stmt, prop);
					srcPropSet.add(prop);
					Long funcID = stmtNode.getFuncId();
					String iden = getPropIdentity(ASTUnderConstruction.idToNode.get(prop), (long) 0);
					name2Func(iden, funcID);
				}
				//it is a return node
				else if(stmtNode instanceof ReturnStatement) {
					srcProp.add(stmt, prop);
					srcPropSet.add(prop);
					Long funcID = stmtNode.getFuncId();
					String iden = getPropIdentity(ASTUnderConstruction.idToNode.get(prop), (long) 0);
					name2Func(iden, funcID);
				}
			} catch(Exception e){
				//System.err.println("Unknown assignment: "+stmt);
			}
			
		}
		
		//get the sink statement
		for(Long sink: PHPCGFactory.sinks) {
			Long stmt = getStatement(sink);
			sinks.add(stmt);
		}
		
		//get the identity of the source class property and global variables
		for(Long src: srcPropSet) {
			ASTNode srcNode = ASTUnderConstruction.idToNode.get(src);
			String iden = getPropIdentity(srcNode, (long) 0);
			name2Stmt.add(iden, src);
		}
		for(Long src: srcGlobalSet) {
			ASTNode srcNode = ASTUnderConstruction.idToNode.get(src);
			String iden = getDIMIdentity(srcNode);
			name2Stmt.add(iden, src);
		}
		System.out.println("original size: "+ PHPCGFactory.call2mtd.totalSize()+" "+PHPCGFactory.mtd2call.totalSize());
		
		validFunc.addAll(PHPCGFactory.topFunIds);
		for(Long func: PHPCGFactory.topFunIds) {
			String path = PHPCGFactory.getDir(func);
			//valid entry point
			if(path.contains("test") || path.contains("Test") || path.contains("vendor")) {
				continue;
			}
			HashSet<Long> callees = getAllcallee(func);
			validFunc.addAll(callees);
		}
		
		int i=0,j=0;
		MultiHashMap<Long, Long> save = new MultiHashMap<Long, Long>();	
		for(Long caller: PHPCGFactory.call2mtd.keySet()) {
			List<Long> targets = PHPCGFactory.call2mtd.get(caller);
			for(Long target: targets) {
				if(validFunc.contains(target)) {
					save.add(caller, target);
					i++;
				}
			}
		}
		
		PHPCGFactory.call2mtd=save;
		//also redefine mtd2call
		PHPCGFactory.mtd2call = new MultiHashMap<Long, Long>();
		for(Long caller: PHPCGFactory.call2mtd.keySet()) {
			List<Long> targets = PHPCGFactory.call2mtd.get(caller);
			for(Long target: targets) {
				PHPCGFactory.mtd2call.add(target, caller);
			}
		}
		
		System.out.println("reduced size: "+ PHPCGFactory.call2mtd.totalSize()+" "+PHPCGFactory.mtd2call.totalSize());
		//     System.out.print("name2Func: "+name2Func.get("1602013::data"));
		
		for(Long key: CSVCFGExporter.cfgSave.keySet()) {
			List<Long> vals = CSVCFGExporter.cfgSave.get(key);
			for(Long val: vals) {
				if(val<=key) {
					continue;
				}
				if(!Edgesize.containsKey(val)) {
					Edgesize.put(val, 1);
				}
				else {
					int number = Edgesize.get(val)+1;
					Edgesize.put(val, number);
				}
			}
		}
	}
	
	private void name2Func(String inter, Long func) {
		if(inter.equals("-2")) {
			return;
		}
		HashSet<Long> related = getAllcaller(func);
		for(Long relate: related) {
			name2Func.add(inter, relate);
		}
	}
	
	//get all function called the input function
	private HashSet<Long> getAllcaller(Long func) {
		if(callee2caller.containsKey(func)) {
			HashSet<Long> ret=new HashSet<Long>(callee2caller.get(func));
			return ret;
		}
		else {
			HashSet<Long> ret=new HashSet<Long>();
			Queue<Long> que = new LinkedList<Long>();
			que.add(func);
			while(!que.isEmpty()) {
				Long node = que.poll();
				ret.add(node);
				if(PHPCGFactory.callee2caller.containsKey(node)) {
					List<Long> callers = PHPCGFactory.callee2caller.get(node);
					for(Long caller: callers) {
						if(!ret.contains(caller)) {
							que.add(caller);
						}
					}
				}
			}
			for(Long node: ret) {
				callee2caller.add(func, node);
			}
			return ret;
		}
	}

	//get all callees of the input function
	private HashSet<Long> getAllcallee(Long func) {
		if(caller2callee.containsKey(func)) {
			HashSet<Long> ret=new HashSet<Long>(caller2callee.get(func));
			return ret;
		}
		else {
			HashSet<Long> ret=new HashSet<Long>();
			Queue<Long> que = new LinkedList<Long>();
			que.add(func);
			while(!que.isEmpty()) {
				Long node = que.poll();
				ret.add(node);
				if(PHPCGFactory.mtd2mtd.containsKey(node)) {
					List<Long> callees = PHPCGFactory.mtd2mtd.get(node);
					for(Long callee: callees) {
						ASTNode target = ASTUnderConstruction.idToNode.get(callee);
						if(!ret.contains(callee)) {
							if(PHPCGFactory.getDir(callee).contains("test") ||
									PHPCGFactory.getDir(callee).contains("Test") ||
									PHPCGFactory.getDir(callee).contains("phpunit") ||
									target.getEnclosingClass()!=null && (target.getEnclosingClass().contains("test") || target.getEnclosingClass().contains("Test")) ||
									target.getEscapedCodeStr()!=null && (target.getEscapedCodeStr().contains("test") || target.getEscapedCodeStr().contains("Test"))) {
								continue;
							}
							que.add(callee);
						}
					}
				}
			}
			for(Long node: ret) {
				caller2callee.add(func, node);
			}
			return ret;
		}
	}

	//check if the source is a taint variable
	private boolean isSource(Long astId) {
		while(PHPCSVEdgeInterpreter.child2parent.containsKey(astId)) {
			Long save = astId;
			astId = PHPCSVEdgeInterpreter.child2parent.get(astId);
			String rootType = ASTUnderConstruction.idToNode.get(astId).getProperty("type");
			//the source is used in assignment
			if(rootType.equals("AST_ASSIGN") ||
					rootType.equals("AST_ASSIGN_OP") ||
					rootType.equals("AST_ASSIGN_REF")) {
				// the source is the right value
				if(PHPCSVEdgeInterpreter.parent2child.get(astId).get(1).equals(save)) {
					return true;
				}
				else {
					return false;
				}
			}
		}
		return false;
	}

	private void constructTaintTree(Node node) {
		traverse(node);
		//getVulnerablePath();
	}

	private void getVulnerablePath() {
		System.out.println("Completed");
		for(Long nodeID: vulStmts) {
			Stack<Long> vulPath = new Stack<Long>();
			vulPath.add(ID2Node.get(nodeID).astId);
			DFS(nodeID, vulPath);
		}
		for(Stack<Long> path: vulPaths) {
			System.out.println(path);
		}
	}
	
	

	private void DFS(Long nodeID, Stack<Long> vulPath) {
		Node node = ID2Node.get(nodeID);
		if(node.parent==null) {
			Stack<Long> tmp = new Stack<Long>();
			while(vulPath.isEmpty()) {
				tmp.push(vulPath.pop());
			}
			vulPaths.add(tmp);
			return;
		}
		Long prt = node.parent;
		vulPath.add(ID2Node.get(prt).astId);
		DFS(prt, vulPath);
		vulPath.pop();
	}

	private Node mergeNode(Long stmt, Set<Long> intra, HashMap<String, Long> inter, Stack<Long> stack) {
		Node node = null;
		if(ID2Node.containsKey(stmt)) {
			//merge the intra- and inter- tainted variables
			node = ID2Node.get(stmt);
			node.intro.addAll(intra);
			for(String key: inter.keySet()) {
				node.inter.put(key, inter.get(key));
			}
			node.caller = stack;
		}
		else {
			node = new Node(stmt, inter, intra, stack);
		}
		
		if(!Edgetimes.containsKey(stmt)) {
			Edgetimes.put(stmt, 1);
		}
		else {
			int number = Edgetimes.get(stmt)+1;
			Edgetimes.put(stmt, number);
		}
		
		return node;
	}
	
	private void clean(Node node) {
		node.inter.clear();
		node.intro.clear();
		node.caller.clear();
	}
	
	//traverse the node's statement
	//@param: one taint node, a boolean value indicating if the current statement is initial source
	//@output: get taint status of this statement, add it to taint tree is it is tainted, and find the next statement ID 
	private boolean traverse(Node node) {
		
		System.out.println("parse stmt: "+" "+node.astId+" "+node.inter+" "+node.intro+" "+node.caller);
		//System.out.println("parse stmt: "+node.nodeId+" "+node.astId);
		Long stmt = node.astId;
		if(stmt==null) {
			System.err.println("Fail to get statement location: "+stmt);
			return false;
		}
		
		boolean taintFunc = false;
		Node nextNode = null;
		
		//iterate the next statement
		if(CSVCFGExporter.cfgSave.containsKey(stmt)) {
			//the function exits here
			//check if the statement has been sanitized
			boolean valid = isvalid(stmt);
			Long topCaller;
			if(node.caller==null || node.caller.isEmpty()) {
				topCaller = (long) 0;
			}
			else {
				topCaller = node.caller.peek();
			}
			
			if(node.inter.isEmpty() && node.intro.isEmpty()) {
				Set<Long> intra=node.intro;
				HashMap<String, Long> inter = node.inter;
				for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
					Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
					Stack<Long> stack =(Stack<Long>) node.caller.clone();
					//update context
					nextNode = mergeNode(next, intra, inter, stack);
					//merge completed and traverse the next statement
					if(Edgetimes.get(next)==Edgesize.get(next)) {
						clean(node);
						traverse(nextNode);
					}
					//loop back
					else if(Edgetimes.get(next)>Edgesize.get(next)) {
						Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
						nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
						clean(node);
						traverse(nextNode);
					}
				}
				return false;
			}
			
			//check if the statement has data flow relationship with taint variables
			HashMap<Long, Long> related = isrelated(stmt, node.intro, node.inter, topCaller);
			//this statement has been sanitized
			if(!valid) {
				HashMap<String, Long> newInter = null;
				//check weather the node needs to be changed
				Set<String> unrelated = RemoveInterTaint(stmt, topCaller, node.inter);
				//remove unrelated global variables and properties
				if(!unrelated.isEmpty()) {
					newInter = new HashMap<String, Long>();
					for(String key: node.inter.keySet()) {
						if(!unrelated.contains(key)) {
							newInter.put(key, node.inter.get(key));
						}
					}
				}
				//the taint status is not changed
				else {
					newInter = node.inter;
				}
				//iterate the next statement
				//only one subsequent node, just traverse
				Set<Long> intra=node.intro;
				for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
					Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
					Stack<Long> stack =(Stack<Long>) node.caller.clone();
					//update context
					nextNode = mergeNode(next, intra, newInter, stack);
					//merge completed and traverse the next statement
					if(Edgetimes.get(next)==Edgesize.get(next)) {
						clean(node);
						traverse(nextNode);
					}
					//loop back
					else if(Edgetimes.get(next)>Edgesize.get(next)) {
						Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
						nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
						clean(node);
						traverse(ID2Node.get(nextNode));
					}
				}
			}
			//the statement is not sanitized
			else{
				//this stmt is source statement, we add taint variables
				if(isSource(stmt)) {
					//node.intro.add(node.astId);
					Set<Long> intra=node.intro;
					HashMap<String, Long> inter = node.inter;
					Set<Long> newIntro = new HashSet<Long>(node.intro);
					Node newNode = addInter(node);
					if(newNode.inter.equals(node.inter)) {
						newIntro.add(node.astId);
					}
					addNode(root, node);
					for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
						Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
						Stack<Long> stack =(Stack<Long>) node.caller.clone();
						//update context
						nextNode = mergeNode(next, intra, inter, stack);
						//merge completed and traverse the next statement
						if(Edgetimes.get(next)==Edgesize.get(next)) {
							clean(node);
							traverse(nextNode);
						}
						//loop back
						else if(Edgetimes.get(next)>Edgesize.get(next)) {
							Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
							nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
							clean(node);
							traverse(nextNode);
						}
					}
				}
				else{
					//if it reaches sink without sanitization, we save the vulnerable path and return.
					if(!related.isEmpty() && sinks.contains(stmt)) {
						vulStmts.add(node.astId);
						//link the callee stmts related to return value to the caller
						for(Long taint: related.keySet()) {
							Long source = related.get(taint);
							Node preNode = ID2Node.get(source);
							addNode(preNode, node);
						}
						return false;
					}
					
					//the stmt contains a function call
					ASTNode stmtNode = ASTUnderConstruction.idToNode.get(stmt);
					//save the caller of the target function
					//this statement is a function call
					if(stmtNode instanceof CallExpressionBase || stmtNode instanceof IncludeOrEvalExpression) {
						Long caller = node.astId;
						Stack<Long> callStack = (Stack<Long>) node.caller.clone();
						callStack.push(caller);
						ArgumentList args = null;
						if(stmtNode instanceof CallExpressionBase) {
							 args = ((CallExpressionBase) stmtNode).getArgumentList();
						}
						//get the target function of this call site
						List<Long> targetFuncs = PHPCGFactory.call2mtd.get(stmt);
						//from argument to the related stmt in caller function
						//built-in function
						if(targetFuncs==null || targetFuncs.isEmpty()){
							Set<Long> intra=node.intro;
							HashMap<String, Long> inter = node.inter;
							for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
								Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
								Stack<Long> stack =(Stack<Long>) node.caller.clone();
								//update context
								nextNode = mergeNode(next, intra, inter, stack);
								//merge completed and traverse the next statement
								if(Edgetimes.get(next)==Edgesize.get(next)) {
									clean(node);
									traverse(nextNode);
								}
								//loop back
								else if(Edgetimes.get(next)>Edgesize.get(next)) {
									Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
									nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
									clean(node);
									traverse(nextNode);
								}
							}
							return false;
						}
						
						//get the out edges of callsite
						int number = PHPCGFactory.call2mtd.get(stmt).size();
						List<Long> retIDs = CSVCFGExporter.cfgSave.get(stmt);
						for(Long retID: retIDs) {
							int ori = Edgesize.get(retID);
							ori = ori-1+number;
							Edgesize.put(retID, ori);
						}
						
						for(Long func: targetFuncs) {
							//the callee is also the caller
							boolean contains = false;
							for(Long id: node.caller) {
								if(ID2Node.containsKey(id)) {
									Long astId = ID2Node.get(id).astId;
									Long callerfunc = ASTUnderConstruction.idToNode.get(astId).getFuncId();
									if(callerfunc.equals(func)) {
										contains=true;
										break;
									}
								}
							}
							if(contains==true) {
								Set<Long> intra=node.intro;
								HashMap<String, Long> inter = node.inter;
								for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
									Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
									Stack<Long> stack =(Stack<Long>) node.caller.clone();
									//update context
									nextNode = mergeNode(next, intra, inter, stack);
									//merge completed and traverse the next statement
									if(Edgetimes.get(next)==Edgesize.get(next)) {
										clean(node);
										traverse(nextNode);
									}
									//loop back
									else if(Edgetimes.get(next)>Edgesize.get(next)) {
										Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
										nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
										clean(node);
										traverse(nextNode);
									}
								}
							}
							
							FunctionDef funcNode = (FunctionDef) ASTUnderConstruction.idToNode.get(func);
							//if it is an empty function, we reach the ret node
							if(funcNode.getContent()==null || funcNode.getContent().size()==0) {
								for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
									Set<Long> intra=node.intro;
									HashMap<String, Long> inter = node.inter;
									Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
									Stack<Long> stack =(Stack<Long>) node.caller.clone();
									//update context
									nextNode = mergeNode(next, intra, inter, stack);
									//merge completed and traverse the next statement
									if(Edgetimes.get(next)==Edgesize.get(next)) {
										clean(node);
										traverse(nextNode);
									}
									//loop back
									else if(Edgetimes.get(next)>Edgesize.get(next)) {
										Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
										nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
										clean(node);
										traverse(nextNode);
									}
								}
								return false;
							}
							
							Long funcID = ASTUnderConstruction.idToNode.get(stmt).getFuncId();
							Long exitID = funcID+2;
							
							//check weather params are tainted
							Set<Long> intro = new HashSet<Long>();
							HashMap<Long, Long> param2caller = new HashMap<Long, Long>();
							
							//this is a function call instead of a require statement
							if(args!=null) {
								for(int i=0; i<args.size(); i++) {
									ASTNode arg = args.getArgument(i); 
									for(Long taint: related.keySet()) {
										//the ith argument is tainted
										if(taint.equals(arg.getNodeId())) {
											if(funcNode.getParameterList().size()<=i) {
												continue;
											}
											//the ith parameter will also be tainted
											ParameterBase param = funcNode.getParameterList().getParameter(i);
											intro.add(param.getNodeId());
											param2caller.put(param.getNodeId(), related.get(taint));
										}
									}
								}
							}
							//get next statement in the target function
							Long nextId = (long) -1;
							//the param is not tainted
							if(intro.isEmpty()) {
								boolean flag = false;
								for(String inter: node.inter.keySet()) {
									//the inter variables are used in the function or not
									for(String key: name2Func.keySet()) {
										//find the key
										if(key.equals(inter) || check(inter, key)==true) {
											if(name2Func.get(key).contains(func)) {
												flag=true;
												break;
											}
										}
									}
								}
								Set<Long> intra=node.intro;
								HashMap<String, Long> inter=node.inter;
								
								//the function is related, we step into it
								if(flag==true) {
									Long nextstmtId = CSVCFGExporter.cfgSave.get(funcNode.getNodeId()+1).get(0);
									ASTNode nextstmt = ASTUnderConstruction.idToNode.get(nextstmtId);
									nextId = nextstmt.getNodeId();
									nextNode = new Node(nextId, node.inter, intro, callStack);
									traverse(nextNode);
								}
								//the function is not related, thus we do not step into it
								else {
									for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
										Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
										Stack<Long> stack =(Stack<Long>) node.caller.clone();
										//update context
										nextNode = mergeNode(next, intra, node.inter, stack);
										//merge completed and traverse the next statement
										if(Edgetimes.get(next)==Edgesize.get(next)) {
											clean(node);
											traverse(nextNode);
										}
										//loop back
										else if(Edgetimes.get(next)>Edgesize.get(next)) {
											Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
											nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
											clean(node);
											traverse(ID2Node.get(nextnext));
										}
									}
									return false;
								}
							}
							//step into the function
							else {
								Set<Long> newIntro = new HashSet<Long>();
								for(Long taintParam: intro) {
									Long prev = param2caller.get(taintParam);
									Node preNode = ID2Node.get(prev);
									nextId = taintParam;
									newIntro.add(nextId);
									nextNode = new Node(nextId, node.inter, newIntro, callStack);
									addNode(preNode, nextNode);
								}
								traverse(nextNode);
							}	
						}
						
					}
					//the statement's right value is a function call
					else if(stmtNode instanceof AssignmentExpression && ((AssignmentExpression) stmtNode).getRight() instanceof CallExpressionBase) {
						Long caller = node.astId;
						Stack<Long> callStack = (Stack<Long>) node.caller.clone();
						callStack.push(caller);
						CallExpressionBase callsite = (CallExpressionBase) ((AssignmentExpression) stmtNode).getRight();
						ArgumentList args = callsite.getArgumentList();
						//get the target function of this call site
						List<Long> targetFuncs = PHPCGFactory.call2mtd.get(callsite.getNodeId());
						//from argument to the related stmt in caller function
						HashMap<Long, Long> param2caller = new HashMap<Long, Long>();
						//it is built-in function
						if(targetFuncs==null || targetFuncs.isEmpty()) {
							//remove tainted variables
							if(related.keySet().isEmpty()) {
								Set<String> unrelated = RemoveInterTaint(stmt, caller, node.inter);
								HashMap<String, Long> newInter = null;
								//remove unrelated global variables and properties
								if(!unrelated.isEmpty()) {
									newInter = new HashMap<String, Long>();
									for(String key: node.inter.keySet()) {
										if(!unrelated.contains(key)) {
											newInter.put(key, node.inter.get(key));
										}
									}
								}
								//the taint status is not changed
								else {
									newInter = node.inter;
								}
								Set<Long> intra=node.intro;
								
								//iterate the next statement
								for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
									Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
									Stack<Long> stack =(Stack<Long>) node.caller.clone();
									//update context
									nextNode = mergeNode(next, intra, newInter, stack);
									//merge completed and traverse the next statement
									if(Edgetimes.get(next)==Edgesize.get(next)) {
										clean(node);
										traverse(nextNode);
									}
									//loop back
									else if(Edgetimes.get(next)>Edgesize.get(next)) {
										Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
										nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
										clean(node);
										traverse(ID2Node.get(nextnext));
									}
								}
								return false;
							}
							//the tainted variables are used as source in built-in function, we think the destination will also be tainted
							else {
								//update context
								Set<Long> save = new HashSet<Long>(node.intro);
								Node tmp = addInter(node);
								if(tmp.inter.equals(node.inter)) {
									save.add(node.astId);
								}
								Set<Long> save1 = save;
								//link node
								for(Long taint: related.keySet()) {
									Long source = related.get(taint);
									Node preNode = ID2Node.get(source);
									addNode(preNode, node);
								}
								//iterate the next statement
								for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
									Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
									Set<Long> intra=node.intro;
									Stack<Long> stack =(Stack<Long>) node.caller.clone();
									//update context
									nextNode = mergeNode(next, save1, tmp.inter, stack);
									//merge completed and traverse the next statement
									if(Edgetimes.get(next)==Edgesize.get(next)) {
										clean(node);
										traverse(nextNode);
									}
									//loop back
									else if(Edgetimes.get(next)>Edgesize.get(next)) {
										Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
										nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
										clean(node);
										traverse(ID2Node.get(nextnext));
									}
								}
								return false;
							}
							
						}
						
						int number = PHPCGFactory.call2mtd.get(callsite.getNodeId()).size();
						List<Long> retIDs = CSVCFGExporter.cfgSave.get(callsite.getNodeId());
						for(Long retID: retIDs) {
							int ori = Edgesize.get(retID);
							ori = ori-1+number;
							Edgesize.put(retID, ori);
						}
						
						for(Long func: targetFuncs) {
							boolean contains = false;
							for(Long id: node.caller) {
								if(ID2Node.containsKey(id)) {
									Long astId = ID2Node.get(id).astId;
									Long callerfunc = ASTUnderConstruction.idToNode.get(astId).getFuncId();
									if(callerfunc.equals(func)) {
										contains=true;
										break;
									}
								}
							}
							//we have already analyzed this function, so we iterate the next stmt
							Set<Long> intra=node.intro;
							HashMap<String, Long> inter = node.inter;
							
							if(contains==true) {
								//iterate the next statement
								for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
									Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
									Stack<Long> stack =(Stack<Long>) node.caller.clone();
									//update context
									nextNode = mergeNode(next, intra, inter, stack);
									//merge completed and traverse the next statement
									if(Edgetimes.get(next)==Edgesize.get(next)) {
										clean(node);
										traverse(ID2Node.get(next));
									}
									//loop back
									else if(Edgetimes.get(next)>Edgesize.get(next)) {
										Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
										nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
										clean(node);
										traverse(ID2Node.get(nextnext));
									}
								}
								return false;
							}
							
							FunctionDef funcNode = (FunctionDef) ASTUnderConstruction.idToNode.get(func);
							if(funcNode.getContent()==null || funcNode.getContent().size()==0) {
								for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
									Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
									
									Stack<Long> stack =(Stack<Long>) node.caller.clone();
									//update context
									nextNode = mergeNode(next, intra, inter, stack);
									//merge completed and traverse the next statement
									if(Edgetimes.get(next)==Edgesize.get(next)) {
										clean(node);
										traverse(ID2Node.get(next));
									}
									//loop back
									else if(Edgetimes.get(next)>Edgesize.get(next)) {
										Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
										mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
										clean(node);
										traverse(ID2Node.get(nextnext));
									}
								}
								return false;
							}
							
							//check weather params are tainted
							Set<Long> intro = new HashSet<Long>();
							for(int i=0; i<args.size(); i++) {
								ASTNode arg = args.getArgument(i); 
								for(Long taint: related.keySet()) {
									//the ith argument is tainted
									if(taint.equals(arg.getNodeId())) {
										if(funcNode.getParameterList().size()<=i) {
											continue;
										}
										//the ith parameter will also be tainted
										ParameterBase param = funcNode.getParameterList().getParameter(i);
										intro.add(param.getNodeId());
										param2caller.put(param.getNodeId(), related.get(taint));
									}
								}
							}
							
							//get next statement of the target function
							//the param is not tainted
							Long nextId = (long) -1;
							if(intro.isEmpty()) {
								HashMap<String, Long> inter1 = node.inter;
								boolean flag = false;
								for(String interName: node.inter.keySet()) {
									//the inter variables are used in the function
									for(String key: name2Func.keySet()) {
										//find the key
										if(key.equals(interName) || check(interName, key)==true) {
											if(name2Func.get(key).contains(func)) {
												flag=true;
												break;
											}
										}
									}
								}
								//the function is related, step into it
								if(flag==true) {
									Long nextstmtId = CSVCFGExporter.cfgSave.get(funcNode.getNodeId()+1).get(0);
									ASTNode nextstmt = ASTUnderConstruction.idToNode.get(nextstmtId);
									nextId = nextstmt.getNodeId();
									nextNode = new Node(nextId, inter1, intro, callStack);
									traverse(nextNode);
								}
								//the function is not related, we traverse the next statement of caller
								else {
									for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
										Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);

										Stack<Long> stack =(Stack<Long>) node.caller.clone();
										//update context
										nextNode = mergeNode(next, intra, inter1, stack);
										//merge completed and traverse the next statement
										if(Edgetimes.get(next)==Edgesize.get(next)) {
											clean(node);
											traverse(ID2Node.get(next));
										}
										//loop back
										else if(Edgetimes.get(next)>Edgesize.get(next)) {
											Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
											nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
											clean(node);
											traverse(ID2Node.get(nextnext));
										}
									}
									return false;
								}
							}
							//the parameters are tainted, step into it
							else {
								Set<Long> newIntro = new HashSet<Long>();
								for(Long taintParam: intro) {
									Long prev = param2caller.get(taintParam);
									Node preNode = ID2Node.get(prev);
									nextId = taintParam;
									newIntro.add(nextId);
									nextNode = new Node(nextId, node.inter, newIntro, callStack);
									addNode(preNode, nextNode);
								}
								traverse(nextNode);
							}
						}
					}
					//the statement is a return statement
					else if(stmtNode instanceof ReturnStatement) {
						
						Long caller = node.caller.peek();
						Node callerNode = ID2Node.get(caller);
						Long callerID = callerNode.astId;
						//next statement of the caller
						List<Long> nextStmts = CSVCFGExporter.cfgSave.get(callerID);
						HashMap<String, Long> inter = node.inter;
						
						//if the return value is tainted
						if(!related.keySet().isEmpty()) {
							//update context
							Set<Long> intra=node.intro;
							intra.add((long) (-1));
							//link the callee stmts related to return value to the caller
							for(Long taint: related.keySet()) {
								Long source = related.get(taint);
								Node preNode = ID2Node.get(source);
								addNode(preNode, callerNode);
							}
							//go to the the exit node
							for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
								Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
								
								Stack<Long> stack =(Stack<Long>) node.caller.clone();
								//update context
								nextNode = mergeNode(next, intra, inter, stack);
								//merge completed and traverse the next statement
								if(Edgetimes.get(next)==Edgesize.get(next)) {
									clean(node);
									traverse(ID2Node.get(next));
								}
								//loop back
								else if(Edgetimes.get(next)>Edgesize.get(next)) {
									Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
									nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
									clean(node);
									traverse(ID2Node.get(nextnext));
								}
							}
							return false;
						}
						//the return value is not tainted
						else {
							for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
								Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
								
								Stack<Long> stack =(Stack<Long>) node.caller.clone();
								//update context
								nextNode = mergeNode(next, new HashSet<Long>(), inter, stack);
								//merge completed and traverse the next statement
								if(Edgetimes.get(next)==Edgesize.get(next)) {
									clean(node);
									traverse(ID2Node.get(next));
								}
								//loop back
								else if(Edgetimes.get(next)>Edgesize.get(next)) {
									Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
									nextNode = mergeNode(nextnext, new HashSet<Long>(), ID2Node.get(next).inter, ID2Node.get(next).caller);
									clean(node);
									traverse(ID2Node.get(nextnext));
								}
							}
							return false;
						}
					}
					//the statement is an assignment
					else {
						Long caller;
						if(node.caller.isEmpty()) {
							caller = (long) 0;
						}
						else {
							caller=node.caller.peek();
						}
						
						
						if(related.keySet().isEmpty()) {
							
							Set<String> unrelated = RemoveInterTaint(stmt, caller, node.inter);
							HashMap<String, Long> newInter = null;
							//remove unrelated global variables and properties
							if(!unrelated.isEmpty()) {
								newInter = new HashMap<String, Long>();
								for(String key: node.inter.keySet()) {
									if(!unrelated.contains(key)) {
										newInter.put(key, node.inter.get(key));
									}
								}
							}
							//the taint status is not changed
							else {
								newInter = node.inter;
							}
							Set<Long> intro = node.intro;
							
							Long stmtId = node.astId;
							for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
								Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
								Stack<Long> stack =(Stack<Long>) node.caller.clone();
								//update context
								nextNode = mergeNode(next, intro, newInter, stack);
								//merge completed and traverse the next statement
								if(Edgetimes.get(next)==Edgesize.get(next)) {
									clean(node);
									traverse(ID2Node.get(next));
								}
								//loop back
								else if(Edgetimes.get(next)>Edgesize.get(next)) {
									Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
									nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
									clean(node);
									traverse(ID2Node.get(nextnext));
								}
							}
							return false;
						}
						else {
							//update context
							Set<Long> save = new HashSet<Long>(node.intro);
							Node tmp = addInter(node);
							if(tmp.inter.equals(node.inter)) {
								save.add(node.astId);
							}
							Set<Long> save1=save;
							//link the callee stmts related to return value to the caller
							for(Long taint: related.keySet()) {
								Long source = related.get(taint);
								Node preNode = ID2Node.get(source);
								addNode(preNode, node);
							}
							//iterate next statement
							Long stmtId = node.astId;
							for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
								Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
								
								Stack<Long> stack =(Stack<Long>) node.caller.clone();
								//update context
								nextNode = mergeNode(next, save, tmp.inter, stack);
								//merge completed and traverse the next statement
								if(Edgetimes.get(next)==Edgesize.get(next)) {
									clean(node);
									traverse(ID2Node.get(next));
								}
								//loop back
								else if(Edgetimes.get(next)>Edgesize.get(next)) {
									Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
									nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
									clean(node);
									traverse(ID2Node.get(nextnext));
								}
							}
						}
					}
				}
			}
		}
		//AST Node FUNC_EXIT
		else if(!node.caller.isEmpty()) {
			Long caller = node.caller.peek();
			if(ID2Node.containsKey(caller)) {
				Node callerNode = ID2Node.get(caller);
				HashMap<String, Long> inter = callerNode.inter;
				Long callerID = ID2Node.get(caller).astId;
				List<Long> nextStmts=CSVCFGExporter.cfgSave.get(callerID);
				//next=CSVCFGExporter.cfgSave.get(next).get(0);
				Stack<Long> callStack = ID2Node.get(caller).caller;
				Set<Long> intro=ID2Node.get(caller).intro;
				//the return value is tainted
				if(!node.intro.isEmpty() && node.intro.contains((long) -1)){
					intro.add(callerID);
				}
				for(int i=0; i<CSVCFGExporter.cfgSave.get(stmt).size(); i++) {
					Long next = CSVCFGExporter.cfgSave.get(stmt).get(i);
					Stack<Long> stack =(Stack<Long>) node.caller.clone();
					//update context
					nextNode = mergeNode(next, intro, inter, stack);
					//merge completed and traverse the next statement
					if(Edgetimes.get(next)==Edgesize.get(next)) {
						clean(callerNode);
						traverse(ID2Node.get(next));
					}
					//loop back
					else if(Edgetimes.get(next)>Edgesize.get(next)) {
						Long nextnext = CSVCFGExporter.cfgSave.get(next).get(1);
						nextNode = mergeNode(nextnext, ID2Node.get(next).intro, ID2Node.get(next).inter, ID2Node.get(next).caller);
						clean(node);
						traverse(ID2Node.get(nextnext));
					}
				}
			}
		}
		
		return taintFunc;
		
	}
	

	private boolean isUsed(Long next, Node context, Long caller) {
		ASTNode node = ASTUnderConstruction.idToNode.get(next);
		//we always step into functions
		if(node instanceof CallExpressionBase || (node instanceof AssignmentExpression && ((AssignmentExpression) node).getRight() instanceof CallExpressionBase)) {
			return true;
		}
		else {
			//the next statement does not use taint variable
			if(!dstProp.containsKey(next) && !dstGlobal.containsKey(next) && isrelated(next, context.intro, context.inter, caller).isEmpty()) {
				return false;
			}
			return true;
		}
	}

	//add inter taint to taint status if the stmt is tainted and the left value is inter variable
	/*
	 * param: node under-construct
	 */
	private Node addInter(Node node) {
		Long astId=node.astId;
		Long caller;
		if(node.caller.isEmpty()) {
			caller=(long) 0;
		}
		else {
			caller = node.caller.peek();
		}
		if(!dstProp.containsKey(astId) && !dstGlobal.containsKey(astId)) {
			return node;
		}
		Node ret = new Node(node);
		HashMap<String, Long> newInter = new HashMap<String, Long>(ret.inter); 
		//the statement contains a dst prop
		if(dstProp.containsKey(astId)) {
			List<Long> dstExps = dstProp.get(astId);
			for(Long dst: dstExps) {
				ASTNode dstNode = ASTUnderConstruction.idToNode.get(dst);
				String identity = getPropIdentity(dstNode, caller);
				newInter.put(identity, node.astId);
			}
		}
		//the statement contains a dst Global variable
		if(dstGlobal.containsKey(astId)) {
			List<Long> dstExps = dstGlobal.get(astId);
			for(Long dst: dstExps) {
				ASTNode dstNode = ASTUnderConstruction.idToNode.get(dst);
				String identity = getDIMIdentity(dstNode);
				newInter.put(identity, node.astId);
			}
		}
		ret.inter=newInter;
		return ret;
	}
	
	//add one node to the taint tree
	/*
	 * param: node1 and node2. Set node2 as the children of node1 
	 */
	private void addNode(Node node1, Node node2) {
		node1.children.add(node2);
	}

	//remove inter taints if they are assigned in unrelated statements 
	/*
	 * @param: unrelated statement, caller and inter set of previous node
	 * @return: a set of unrelated global variables and properties 
	 */
	private Set<String> RemoveInterTaint(Long stmt, Long caller, HashMap<String, Long> inter) {
		if(ID2Node.containsKey(caller)) {
			caller = ID2Node.get(caller).astId;
		}
		Set<String> ret = new HashSet<String>();
		//global variable is assigned
		if(dstGlobal.containsKey(stmt)) {
			//location of global expression
			List<Long> dstExps = dstGlobal.get(stmt);
			for(Long exp: dstExps) {
				ASTNode globalNode = ASTUnderConstruction.idToNode.get(exp);
				String globalName = getDIMIdentity(globalNode);
				for(String interTaint: inter.keySet()) {
					if(interTaint.startsWith(globalName) || globalName.startsWith(interTaint)) {
						//inter.remove(interTaint);
						ret.add(interTaint);
					}
				}
			}
		}
		//global property is assigned
		if(dstProp.containsKey(stmt)) {
			//location of prop expression
			List<Long> dstExps = dstProp.get(stmt);
			for(Long exp: dstExps) {
				ASTNode propNode = ASTUnderConstruction.idToNode.get(exp);
				String propName = getPropIdentity(propNode, caller);
				for(String interTaint: inter.keySet()) {
					if(check(propName, interTaint)) {
						//inter.remove(interTaint);
						ret.add(interTaint);
					}
				}
			}
		}
		return ret;
	}

	/*
	 * @param: one statement
	 * @return: true if the statement is sanitized; otherwise false 
	 */
	private boolean isvalid(Long stmt) {
		if(sqlSanitizers.contains(stmt)) {
			return false;
		}
		return true;
	}
	
	/*
	 * @param: the statement ID, the intro set and inter set of previous node, and caller
	 * check if the statement is tainted under the given context
	 * @@return: the taint variable in stmts and and its corresponding related statements  
	 */
	private HashMap<Long, Long> isrelated(Long stmt, Set<Long> intro, HashMap<String, Long> inter, Long caller) {
		if(ID2Node.containsKey(caller)) {
			caller = ID2Node.get(caller).astId;
		}
		HashMap<Long, Long> relatedNodes = new HashMap<Long, Long>();
		
		//check intro-data flow relationship
		for(Long nodeID: intro) {
			Node introNode = ID2Node.get(nodeID);
			if(introNode==null) {
				System.out.println("ASTID: "+nodeID);
				continue;
			}
			Long taint = introNode.astId;
			//we do not support loop currently
			if(taint>stmt) {
				continue;
			}
			//check if the statement has intro-data flow relationship with taint variable
			if(DDG.rels.containsKey(taint)) {
				//get all the related statements of the taint
				for(Pair<Long, String> tmp: DDG.rels.get(taint)) {
					//the stmt has deta flow relationship with taint statement
					if(tmp.getL().equals(stmt)) {
						ASTNode taintNode = ASTUnderConstruction.idToNode.get(taint);
						//the taint statement is a assignment
						if(taintNode.getProperty("type").equals("AST_ASSIGN") || taintNode.getProperty("type").equals("AST_ASSIGN_OP") || taintNode.getProperty("type").equals("AST_ASSIGN_REF")) {
							ASTNode leftValue = ((AssignmentExpression) taintNode).getLeft();
							//the symbol in taint statement is an array
							if(leftValue.getProperty("type").equals("AST_DIM")) {
								String symbol1 = getDIMIdentity(leftValue);
								//get the source dim in current stmt
								if(srcDim.containsKey(stmt)) {
									//get the locations of dim expressions in stmt
									List<Long> dims = srcDim.get(stmt);
									for(Long dim: dims) {
										ASTNode rightValue = ASTUnderConstruction.idToNode.get(dim);
										String symbol2 = getDIMIdentity(rightValue);
										//this srcdim in current statement is related to taint symbol
										if(symbol1.startsWith(symbol2) || symbol2.startsWith(symbol1)) {
											relatedNodes.put(dim, nodeID);
										}
									}
								}
							}
							//the taint variable is not an array
							else {
								ASTNode stmtNode = ASTUnderConstruction.idToNode.get(stmt);
								if(stmtNode instanceof CallExpressionBase) {
									String tag = tmp.getR();
									ArgumentList args = ((CallExpressionBase) stmtNode).getArgumentList();
									for(int i=0; i<args.size(); i++) {
										ASTNode arg = args.getArgument(i);
										//the taint variable is used as argument 
										if(arg instanceof Variable && ((Variable) arg).getNameExpression().getEscapedCodeStr().equals(tag)) {
											relatedNodes.put(arg.getNodeId(), nodeID);
										}
									}
								}
								else if(stmtNode instanceof AssignmentExpression && ((AssignmentExpression) stmtNode).getRight() instanceof CallExpressionBase) {
									String tag = tmp.getR();
									ArgumentList args = ((CallExpressionBase) ((AssignmentExpression) stmtNode).getRight()).getArgumentList();
									for(int i=0; i<args.size(); i++) {
										ASTNode arg = args.getArgument(i);
										//the taint variable is used as argument 
										if(arg instanceof Variable && ((Variable) arg).getNameExpression().getEscapedCodeStr().equals(tag)) {
											relatedNodes.put(arg.getNodeId(), nodeID);
										}
									}
								}
								//
								else if(stmtNode instanceof AssignmentExpression){
									Expression leftNode = ((AssignmentExpression) stmtNode).getLeft();
									if(leftNode instanceof Variable) {
										relatedNodes.put(leftNode.getNodeId(), nodeID);
									}
									
								}
							}
						}
					}
				}
			}
		}
		
		//the stmt contains a source prop
		if(srcProp.containsKey(stmt)) {
			//get the property used in this statement
			List<Long> props = srcProp.get(stmt);
			for(Long propId: props) {
				ASTNode propNode=ASTUnderConstruction.idToNode.get(propId);
				//get the identity of the property
				String srcProp = getPropIdentity(propNode, caller);
				for(String interTaint: inter.keySet()) {
					if(check(srcProp, interTaint)) {
						relatedNodes.put(propId, inter.get(interTaint));
					}
				}
			}
		}
		
		//the stmt is a return statement and it returns a class, we directly get its identity from comments
		if(ASTUnderConstruction.idToNode.get(stmt) instanceof ReturnStatement) {
			//get the function of return statement
			ReturnStatement retNode = (ReturnStatement) ASTUnderConstruction.idToNode.get(stmt);
			Long funcId = retNode.getFuncId();
			//the function returns a class
			if(PHPCGFactory.retCls.containsKey(funcId)) {
				Long classID = PHPCGFactory.retCls.get(funcId);
				String srcProp = classID+"::-1";
				for(String interTaint: inter.keySet()) {
					if(check(srcProp, interTaint)) {
						relatedNodes.put((long) -1, inter.get(interTaint));
					}
				}
			}
		}
		
		//the stmt contains a source global variable
		if(srcGlobal.containsKey(stmt)) {
			List<Long> globals = srcGlobal.get(stmt);
			for(Long globalId: globals) {
				ASTNode globalNode = ASTUnderConstruction.idToNode.get(globalId);
				String srcGlobal = getDIMIdentity(globalNode);
				for(String interTaint: inter.keySet()) {
					if(interTaint.startsWith(srcGlobal) || srcGlobal.startsWith(interTaint)) {
						relatedNodes.put(globalId, inter.get(interTaint));
					}
				}
			}
		}
		
		return relatedNodes;
	}
	
	//check if two properties represent the same variable
	private boolean check(String srcProp, String interTaint) {
		if(srcProp.contains("-1") || interTaint.contains("-1")) {
			srcProp = srcProp.replace("-1", "");
			interTaint = interTaint.replace("-1", "");
			if(srcProp.contains(interTaint) || interTaint.contains(srcProp)) {
				return true;
			}
		}
		else {
			if(srcProp.equals(interTaint)) {
				return true;
			}
		}
		return false;
	}
	
	
	//get the identity of property variable
	/*
	 * @param: propert ast ID, caller
	 * @return: the identity of the property. e.g., $a->b=>astnode(a)::b; returns -1 if cannot get the identity
	 */
	private String getPropIdentity(ASTNode node, Long caller) {
		if(node instanceof PropertyExpression) {
			String objValue="-1", propValue="*";
			
			//get prop's class
			Expression objNode = ((PropertyExpression) node).getObjectExpression();
			String type = objNode.getProperty("type");
			switch(type) {
			//$this->prop
			case "AST_VAR":
				if(((Variable) objNode).getNameExpression().getEscapedCodeStr().equals("this")) {
					objValue = objNode.getEnclosingClass();
					String namespace = objNode.getEnclosingNamespace();
					objValue = PHPCGFactory.getClassId(objValue, objNode.getNodeId(), namespace).toString();
				}
				break;
			//func()->prop
			case "AST_CALL":
			case "AST_METHOD_CALL":
			case "AST_STATIC_CALL":
				if(PHPCGFactory.call2mtd.containsKey(objNode.getNodeId())) {
					Long targetFuncID = PHPCGFactory.call2mtd.get(objNode.getNodeId()).get(0);
					if(PHPCGFactory.retCls.containsKey(targetFuncID)){
						objValue = PHPCGFactory.retCls.get(targetFuncID).toString(); 
					}
				}
				break;
			
			}
			//we do not know the objValue yet, thus we parse it value
			if(objValue.equals("-1")) {
				ParseVar parsevar = new ParseVar();
				parsevar.init(1, false, "");
				String className = parsevar.IntroDataflow(objNode.getNodeId()).iterator().next();
				if(className.startsWith("$")) {
					try {
						//the class is returned from a known target function
						Long classId = Long.parseLong(className.substring(1, className.length() - 1));
						ASTNode classNode = ASTUnderConstruction.idToNode.get(classId);
						if(classNode instanceof CallExpressionBase) {
							if(PHPCGFactory.call2mtd.containsKey(classNode.getNodeId())) {
								Long targetFuncID = PHPCGFactory.call2mtd.get(classNode.getNodeId()).get(0);
								if(PHPCGFactory.retCls.containsKey(targetFuncID)){
									objValue = PHPCGFactory.retCls.get(targetFuncID).toString(); 
								}
							}
						}
					}catch(Exception e) {
						
					}
				}
				else {
					objValue = className;
				}
				
			}
			
			//get prop's name
			Expression propNode = ((PropertyExpression) node).getPropertyExpression();
			//the prop name is an identifier
			if(propNode.getProperty("type").equals("string")) {
				propValue = propNode.getEscapedCodeStr();
			}
			//the prop name is a variable and it is assigned by the parameter
			else if(propNode.getProperty("type").equals("AST_VAR")) {
				//get the variable name of prop
				String varName = ((Variable) propNode).getNameExpression().getEscapedCodeStr();
				//get prop variable's function
				FunctionDef currentFunc = (FunctionDef) ASTUnderConstruction.idToNode.get(propNode.getFuncId());
				ParameterList paramList = currentFunc.getParameterList();
				if(paramList==null) {
					System.out.println("null param: "+currentFunc.getNodeId());
					return "-1";
				}
				for(int i=0; i<paramList.size(); i++) {
					Parameter param = (Parameter) paramList.getParameter(i);
					String paramName = param.getName();
					//i'th param name is equal to prop's variable name
					if(paramName.equals(varName) && caller!=0) {
						CallExpressionBase callerNode = (CallExpressionBase) ASTUnderConstruction.idToNode.get(caller);
						ArgumentList argList = (ArgumentList) callerNode.getArgumentList();
						//get the i'th argument value
						Expression arg = argList.getArgument(i);
						if(arg.getProperty("type").equals("string")) {
							propValue = arg.getEscapedCodeStr();
						}
					}
				}
			}
			
			//we at least know the prop name
			if(!propValue.equals("*")) {
				return objValue+"::"+propValue;
			}
		}
		return "-2";
	}
	
	//get the identity of DIM variable
	/*
	 * @param: node($a[b][c])
	 * @return a$b$c
	 */
	public String getDIMIdentity(ASTNode node) {
		//$a[b][c], we do not return $a or $a[b], instead we only return $a[b][c]
		if(PHPCSVEdgeInterpreter.child2parent.containsKey(node.getNodeId())) {
			//the the parent of DIM variable
			ASTNode parent = ASTUnderConstruction.idToNode.get(PHPCSVEdgeInterpreter.child2parent.get(node.getNodeId()));
			//DIM's parent is a a DIM variable
			if(parent instanceof ArrayIndexing) {
				return "-1";
			}
		}
		while(node instanceof ArrayIndexing) {
			node = ((ArrayIndexing) node).getArrayExpression();
		}
		//AST_DIM. AST_VAR, AST_NAME
		Long constantId = node.getNodeId()+2;
		String identity="";
		while(true) {
			ASTNode constant = ASTUnderConstruction.idToNode.get(constantId);
			if(constant.getEscapedCodeStr()==null || constant.getEscapedCodeStr().isEmpty()) {
				break;
			}
			identity = identity+constant.getEscapedCodeStr()+"$";
			constantId = constantId+1;
		}
		//fail to get DIM identity
		if(identity.equals("")) {
			return "-1";
		}
		return identity;
	} 

	//get the statement of taint node
	/*
	 * @param: astID
	 * @return: <statement, stmtList>
	 */
	private Long getStatement(Long astId) {
		while(true) {
			//check if astId is cfg node
			if(cfgNode.contains(astId)) {
				return astId;
			}
			//get astId's parent
			if(!PHPCSVEdgeInterpreter.child2parent.containsKey(astId)) {
				return null;
			}
			astId = PHPCSVEdgeInterpreter.child2parent.get(astId);
			//check if the ast node is a CFG node
		}
	}
}








package cg;
import tools.php.ast2cpg.PHPCSVEdgeInterpreter;

import java.io.File;
import java.io.IOException;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedHashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import ast.ASTNode;
import ast.expressions.ArgumentList;
import ast.expressions.AssignmentExpression;
import ast.expressions.BinaryOperationExpression;
import ast.expressions.CallExpressionBase;
import ast.expressions.ClassConstantExpression;
import ast.expressions.Constant;
import ast.expressions.Expression;
import ast.expressions.Identifier;
import ast.expressions.NewExpression;
import ast.expressions.PropertyExpression;
import ast.expressions.StaticPropertyExpression;
import ast.expressions.StringExpression;
import ast.expressions.Variable;
import ast.php.expressions.MethodCallExpression;
import ast.php.expressions.StaticCallExpression;
import ast.php.statements.StaticVariableDeclaration;
import ast.statements.jump.ReturnStatement;
import ddg.DataDependenceGraph.DDG;
import inputModules.csv.csv2ast.ASTUnderConstruction;
import misc.MultiHashMap;
import ast.php.functionDef.*;

public class ParseVar {
	private  long varId;
	//type of function name variable must be String
	private Set<String> varValue;
	private boolean isClass;
	private Set<Long> involvedIds;
	private Queue<Long> queue;
	private static MultiHashMap<String, String> relations = new MultiHashMap<String, String>();
	private static MultiHashMap<Long, String> cache2 = new MultiHashMap<Long, String>();
	public static MultiHashMap<Long, Long> func2Ret = new MultiHashMap<Long, Long>();
	
	//send node to be parsed
	public void init(long varId, boolean isclass, String global){
		this.varId = varId;
		varValue = new LinkedHashSet<String>();
		involvedIds = new HashSet<Long>();
		queue = new LinkedList<Long>();
		queue.offer(varId);
		this.isClass = isclass;
	}
	
	
	
	public static void ParseInterRelationship() {
		//parse assignment
		for(Long assign: PHPCSVEdgeInterpreter.collectAssign) {
			System.err.println("Parsing assignment: "+assign+" "+ PHPCSVEdgeInterpreter.collectAssign.size());
			AssignmentExpression assignNode = (AssignmentExpression) ASTUnderConstruction.idToNode.get(assign);
			Expression leftNode = (Expression) (assignNode.getLeft());
			Expression rightNode = (Expression) (assignNode.getRight());
			//get the left value
			String leftValue = parseInterRelation(leftNode);
			
			//get the right value
			if(rightNode==null) {
				continue;
			}
			String rightValue = "*";
			switch(rightNode.getProperty("type")) {
			//get the class directly
			case "AST_NEW":
				//System.err.println("AST_NEW: "+rightNode.getNodeId());
				Expression classNode = ((NewExpression) rightNode).getTargetClass();
				if(classNode==null || classNode.getProperty("type")==null) {
					break;
				}
				if(classNode.getProperty("type").equals("AST_NAME")) {
					StringExpression classNameNode = ((Identifier) classNode).getNameChild();
					String className = classNameNode.getEscapedCodeStr();
					String namespace = classNode.getEnclosingNamespace();
					Long classId = PHPCGFactory.getClassId(className, classNode.getNodeId(), namespace);
					if(classId!=-1) {
						rightValue = "@"+classId;
					}
				}
				break;
			//perform inter-procedural analysis
			case "AST_VAR":
			case "AST_STATIC_PROP":
			case "AST_PROP":
			case "AST_CALL":
			case "AST_STATIC_CALL":
			case "AST_METHOD_CALL":
				rightValue = "#"+rightNode.getNodeId();
			}
			
			if(assign==1131151) {
				System.err.println("1131151 "+leftValue+" "+rightValue);
			}
			
			if(!leftValue.equals("*") && !rightValue.equals("*")) {
				relations.add(leftValue, rightValue);
			}
		}
		
		//class A{$a = new class();}
		//parse static properties assignment
		for(Long staticProp: PHPCSVEdgeInterpreter.collectStatic) {
			System.err.println("Parsing static assignment: "+staticProp+" "+ PHPCSVEdgeInterpreter.collectStatic.size());
			StaticVariableDeclaration staticPropNode = (StaticVariableDeclaration) ASTUnderConstruction.idToNode.get(staticProp);
			String leftValue="-1", rightValue="*";
			
			//parse left value
			Variable var = staticPropNode.getNameChild();
			if(var.getProperty("type").equals("AST_VAR")) {
				String varName = var.getNameExpression().getEscapedCodeStr();
				String className = var.getEnclosingClass();
				
				//it is a static class property
				if(className==null || className.isEmpty()) {
					continue;
				}
				//leftValue = className+"::"+varName;
				String namespace = var.getEnclosingNamespace();
				Long classId = PHPCGFactory.getClassId(className, var.getNodeId(), namespace);
				leftValue=classId.toString()+"::"+varName;
			}
			//parse right value
			Expression value = staticPropNode.getDefault();
			if(value==null) {
				continue;
			}
			if(value.getProperty("type").equals("AST_CONST")) {
				Identifier rightNode = ((Constant) value).getIdentifier();
				String className = rightNode.getNameChild().getEscapedCodeStr();
				String namespace = rightNode.getEnclosingNamespace();
				Long classId = PHPCGFactory.getClassId(className, value.getNodeId(), namespace);
				if(classId!=-1) {
					rightValue = "@"+classId;
				}
			}
			
			if(!leftValue.equals("*") && !rightValue.equals("*")) {
				relations.add(leftValue, rightValue);
			}
		}
		
		//return $var;
		//parse variables returned from functions
		for(Long returnNodeId: PHPCSVEdgeInterpreter.collectRet) {
			System.err.println("Parsing return statements: "+returnNodeId+" "+ PHPCSVEdgeInterpreter.collectRet.size());
			ReturnStatement returnNode = (ReturnStatement) ASTUnderConstruction.idToNode.get(returnNodeId);
			Long funcId = returnNode.getFuncId();
			Expression ReturnValueNode = returnNode.getReturnExpression();
			if(ReturnValueNode==null) {
				continue;
			}
			func2Ret.add(funcId, ReturnValueNode.getNodeId());
			String returnValue = "*";
			
			//get current function name (leftValue)
			Long funcDeclNodeId = returnNodeId;
			do {
				funcDeclNodeId = PHPCSVEdgeInterpreter.child2parent.get(funcDeclNodeId);
				if(ASTUnderConstruction.idToNode.get(funcDeclNodeId) instanceof FunctionDef) {
					break;
				}
			}while(true);
			//System.err.println("Return Node: "+returnNodeId+" "+funcDeclNodeId);
			FunctionDef funcDeclNode = (FunctionDef) ASTUnderConstruction.idToNode.get(funcDeclNodeId);
			String funcDecName = funcDeclNode.getName()+"()";
			//it is method
			if(returnNode.getEnclosingClass()!=null && !returnNode.getEnclosingClass().isEmpty()) {
				String className = returnNode.getEnclosingClass();
				String namespace = returnNode.getEnclosingNamespace();
				Long classId = PHPCGFactory.getClassId(className, funcDeclNodeId, namespace);
				if(classId == -1) {
					continue;
				}
				funcDecName = classId.toString()+"::"+funcDecName;
			}
			
			//get return value
			if(ReturnValueNode != null) {
				String type = ReturnValueNode.getProperty("type");
				//get class from new
				if(type.equals("AST_NEW")){
					Expression classNode = ((NewExpression) ReturnValueNode).getTargetClass();
				
					if(classNode.getProperty("type")!=null && classNode.getProperty("type").equals("AST_NAME")) {
						StringExpression classNameNode = ((Identifier) classNode).getNameChild();
						String callClassName = classNameNode.getEscapedCodeStr();
						String callNamespace = classNode.getEnclosingNamespace();
						if(PHPCGFactory.getClassId(callClassName, classNode.getNodeId(), callNamespace)!=-1) {
							returnValue = "@"+PHPCGFactory.getClassId(callClassName, classNode.getNodeId(), callNamespace);
						}
						if(!funcDecName.equals("*")) {
							relations.add(funcDecName, "@"+returnValue);
						}
						continue;
					}
				}
				//get class from comment
				if(PHPCGFactory.retCls.containsKey(funcId)) {
					Long classId = PHPCGFactory.retCls.get(funcId);
					Set<Long> allChild = PHPCGFactory.getAllChild(classId);
					allChild.add(classId);
					for(Long clsId: allChild) {
						if(!funcDecName.equals("*")) {
							relations.add(funcDecName, "@"+clsId);
						}
					}
					continue;
				}
				//do not get class
				if(returnValue.equals("*")) {
					returnValue = "#"+ReturnValueNode.getNodeId();
				}
				if(!funcDecName.equals("*")) {
					relations.add(funcDecName, returnValue);
				}
			}
		}
		
		//parameters => arguments
		//pasre variables from constructor parameters
		for(Long newId: PHPCSVEdgeInterpreter.collectNew) {
			System.err.println("Parsing new statements: "+newId+" "+ PHPCSVEdgeInterpreter.collectNew.size());
			NewExpression newNode = (NewExpression) ASTUnderConstruction.idToNode.get(newId);
			String funcValue="*", leftValue="*", rightValue="*";
			
			Expression newClassNode = newNode.getTargetClass();
			if(newClassNode==null || newClassNode.getProperty("type")==null) {
				continue;
			}
			if(newClassNode.getProperty("type").equals("AST_NAME")) {
				StringExpression classNameNode = ((Identifier) newClassNode).getNameChild();
				funcValue = classNameNode.getEscapedCodeStr();
				String namespace = newClassNode.getEnclosingNamespace();
				Long classId = PHPCGFactory.getClassId(funcValue, newClassNode.getNodeId(), namespace);
				if(classId==-1) {
					continue;
				}
				funcValue = classId+"::"+"__construct()";	
			}
			
			//parse each parameter
			ArgumentList argList = (ArgumentList) newNode.getArgumentList();
			int size = argList.size();
			for(int i=0; i<size; i++) {
				leftValue = funcValue+"~"+i;
				Expression arg = argList.getArgument(i);
				String type = arg.getProperty("type");
				switch(type) {
				case "AST_NEW":
					Expression classNode = ((NewExpression) arg).getTargetClass();
					if(classNode.getProperty("type").equals("AST_NAME")) {
						StringExpression classNameNode = ((Identifier) classNode).getNameChild();
						String callClassName = classNameNode.getEscapedCodeStr();
						String callNamespace = classNode.getEnclosingNamespace();
						if(PHPCGFactory.getClassId(callClassName, classNode.getNodeId(), callNamespace)!=-1) {
							rightValue = "@"+PHPCGFactory.getClassId(callClassName, classNode.getNodeId(), callNamespace);
						}
					}
					break;
				default:
					rightValue = "#"+arg.getNodeId();
				}
				if(!leftValue.equals("*") && !rightValue.equals("*")) {
					relations.add(leftValue, rightValue);
				}
			}
		}
		
		//parameters => arguments
		//parse variables from function parameters
		for(Long funcDecId: PHPCSVEdgeInterpreter.collectFuncCall) {
			System.err.println("Parsing calling nodes: "+funcDecId+" "+ PHPCSVEdgeInterpreter.collectFuncCall.size());
			CallExpressionBase funcDefNode = (CallExpressionBase) ASTUnderConstruction.idToNode.get(funcDecId);
			String funcValue="*", leftValue="*", rightValue="*";
			
			funcValue = parseInterRelation(funcDefNode);
			//built-in functions
			if(funcValue.equals("*")) {
				//System.err.println("Unsupported calling function type: "+funcDefNode);
				continue;
			}
			//parse each parameter
			ArgumentList argList = (ArgumentList) funcDefNode.getArgumentList();
			int size = argList.size();
			for(int i=0; i<size; i++) {
				leftValue = funcValue+"~"+i;
				Expression arg = argList.getArgument(i);
				String type = arg.getProperty("type");
				//get the argument name
				switch(type) {
				case "AST_NEW":
					Expression classNode = ((NewExpression) arg).getTargetClass();
					if(classNode.getProperty("type").equals("AST_NAME")) {
						StringExpression classNameNode = ((Identifier) classNode).getNameChild();
						String callClassName = classNameNode.getEscapedCodeStr();
						String callNamespace = classNode.getEnclosingNamespace();
						if(PHPCGFactory.getClassId(callClassName, classNode.getNodeId(), callNamespace)!=-1) {
							rightValue = "@"+PHPCGFactory.getClassId(callClassName, classNode.getNodeId(), callNamespace);
						}
					}
					break;
				default:
					rightValue = "#"+arg.getNodeId();
				}
				if(!leftValue.equals("*") && !rightValue.equals("*")) {
					relations.add(leftValue, rightValue);
				}
			}
		}
	}
	
	//get the identity of a ASTNode 
	public static String parseInterRelation(ASTNode Node) {
		String type = Node.getProperty("type");
		String ret = "*";
		switch(type) {
		case "AST_MAGIC_CONST":
			String magicFlags = Node.getFlags();
			switch(magicFlags) {
				case "MAGIC_CLASS":
					ret = (Node.getEnclosingClass());
					break;
				case "MAGIC_FUNCTION":
					ret = ((((FunctionDef) ASTUnderConstruction.idToNode.get(Node.getFuncId())).getName()));
					break;
			}
			break;
		case "AST_CONST":
			Identifier constNode = ((Constant)Node).getIdentifier();
			String constValue = constNode.getNameChild().getEscapedCodeStr();
			if(constValue.equals("null")) {
				ret = "";
			}
			else {
				ret = constValue;
			}
			break;
		case "AST_VAR":
			if(((Variable) Node).getNameExpression().getProperty("type").equals("string")) {
				Expression varName = ((Variable) Node).getNameExpression();
				if(!PHPCGFactory.globalMap.containsKey(varName.getEscapedCodeStr())) {
					break;
				}
				ret = varName.getEscapedCodeStr();
			}
			break;
		case "AST_PROP":
			PropertyExpression propNode = (PropertyExpression) Node;
			Expression propClassNode = propNode.getObjectExpression();
			Expression propVariableNode = propNode.getPropertyExpression();
			String propClass = "-1", propName = "*";
			
			//$var->prop, get class of $var
			if(propClassNode.getProperty("type").equals("AST_VAR")) {
				if(((Variable) propClassNode).getNameExpression().getEscapedCodeStr().equals("this")) {
					propClass = propClassNode.getEnclosingClass();
					String namespace = propClassNode.getEnclosingNamespace();
					propClass = PHPCGFactory.getClassId(propClass, propClassNode.getNodeId(), namespace).toString();
				}
			}
			//$var->prop, get prop, we only accept strings
			if(propVariableNode.getProperty("type").equals("string")) {
				propName = propVariableNode.getEscapedCodeStr();
			}
			
			//we do not accept properties who have unknown names
			if(!propName.equals("*")) {
				ret = propClass+"::"+propName;
			}
			break;
		case "AST_STATIC_PROP":
			StaticPropertyExpression staticPropNode = (StaticPropertyExpression) Node;
			Expression staticPropClassNode = staticPropNode.getClassExpression();
			Expression staticPropVariableNode = staticPropNode.getPropertyExpression();
			String staticPropClass = "-1", staticPropName = "*";
			
			//class::prop, get class
			if(staticPropClassNode.getProperty("type").equals("AST_NAME")) {
				StringExpression classNameNode = ((Identifier) staticPropClassNode).getNameChild();
				String className = classNameNode.getEscapedCodeStr();
				String namespace = staticPropNode.getEnclosingNamespace();
				if(className.equals("self") || className.equals("static") || className.equals("parent")) {
					staticPropClass = staticPropNode.getEnclosingClass();
					Long staticId = PHPCGFactory.getClassId(staticPropClass, staticPropClassNode.getNodeId(), namespace);
					if(className.equals("parent")) {
						staticId = PHPCGFactory.ch2prt.get(staticId).get(0);
					}
					staticPropClass = staticId.toString();
				}
				else {
					staticPropClass = className;
					staticPropClass = PHPCGFactory.getClassId(staticPropClass, staticPropClassNode.getNodeId(), namespace).toString();
				}
			}
			
			//class::prop get property
			if(staticPropVariableNode.getProperty("type").equals("string")) {
				staticPropName = staticPropVariableNode.getEscapedCodeStr();
			}
			if(!staticPropName.equals("*")) {
				ret = staticPropClass+"::"+staticPropName;
			}
			break;
		case "AST_METHOD_CALL":
			MethodCallExpression methodCallNode = (MethodCallExpression) Node;
			Expression object = methodCallNode.getTargetObject();
			Expression func = methodCallNode.getTargetFunc();
			String objectName="-1", funcName="*";
			
			//class name
			if(object.getProperty("type").equals("AST_VAR")) {
				if(((Variable) object).getNameExpression().getEscapedCodeStr()==null) {
					System.err.println("840: "+object.getNodeId());
				}
				else if(((Variable) object).getNameExpression().getEscapedCodeStr().equals("this")) {
					objectName = object.getEnclosingClass();
					String namespace = object.getEnclosingNamespace();
					objectName = PHPCGFactory.getClassId(objectName, object.getNodeId(), namespace).toString();
				}
			}
			//function name
			if(func.getProperty("type").equals("string")) {
				funcName = func.getEscapedCodeStr();
			}
			
			//We do not expect the method name is a variable
			if(!funcName.equals("*")) {
				ret = objectName+"::"+funcName+"()";
			}
			break;
		case "AST_STATIC_CALL":
			StaticCallExpression staticMethodCallNode = (StaticCallExpression) Node;
			Expression classNode = staticMethodCallNode.getTargetClass();
			Expression funcNode = staticMethodCallNode.getTargetFunc();
			String className = "-1", funName = "*";
			
			//get class name
			if(classNode.getProperty("type").equals("AST_NAME")) {
				StringExpression classNameNode = ((Identifier) classNode).getNameChild();
				className = classNameNode.getEscapedCodeStr();
				String namespace = staticMethodCallNode.getEnclosingNamespace();
				if(className.equals("self") || className.equals("static") || className.equals("parent")) {
					className = staticMethodCallNode.getEnclosingClass();
					//System.err.println("static name: "+className);
					Long classId = PHPCGFactory.getClassId(className, classNode.getNodeId(), namespace);
					if(className.equals("parent")) {
						classId = PHPCGFactory.ch2prt.get(classId).get(0);
					}
					className = classId.toString();
				}
				else {
					className = PHPCGFactory.getClassId(className, classNode.getNodeId(), namespace).toString();
				}
			}
			
			//get func name
			if(funcNode.getProperty("type").equals("string")) {
				funName = funcNode.getEscapedCodeStr();
			}
			//we can always get the class of receiver object, if the receiver object is literally knnown
			if(!className.equals("-1") && !funName.equals("*")) {
				ret = className+"::"+funName+"()";
			}
			break;
		case "AST_CALL":
			CallExpressionBase callNode = (CallExpressionBase) Node;
			Expression functionNode = callNode.getTargetFunc();
			String callFunc = "*";
			
			if(functionNode.getProperty("type").equals("ASTName")) {
				StringExpression funcNameNode = ((Identifier) functionNode).getNameChild();
				callFunc = funcNameNode.getEscapedCodeStr();
			}
			if(!callFunc.equals("*")) {
				ret = callFunc+"()";
			}
			break;
		}
		return ret;
	}



	public Set<String> getVar() {
		//store value for each variable we have parse;
		return varValue;
	}
	
	// get the value of an AST node
	/*
	 * the node represents a class: returns the AST ID of the class
	 * the node represents a value: returnns the regex value  
	 */
	public void handle() {
		Set<Long> save = new HashSet<Long>();
		while(!queue.isEmpty()) {
			Long id = queue.poll();
			save.add(id);
			
			//first, get the value from expression
			boolean isExp=false;
			Set<String> expValue = new HashSet<String>(ParseExp(ASTUnderConstruction.idToNode.get(id)));
			for(String value: expValue) {
				if(!value.startsWith("$")) {
					varValue.add(value);
					isExp=true;
				}
			}
			if(isExp) {
				continue;
			}
			
			//then, perform intro-data flow analysis
			//get variable's name
			Set<String> introValue = IntroDataflow(id);
			
			//it is a variable defined outside the function and it is the root exp node
			if(introValue.isEmpty()) {
				introValue.add("$"+id.toString()+"$");
			}
			for(String value: introValue) {
				//it is a variable defined within the function
				if(!value.contains("$")) {
					//TODO get the classId of value and put it in varValue
					varValue.add(value);
					continue;
				}
				//it is a variable defined outside the function
				else {
					//we do not expect string operations when parsing the receiver objects.
					if(isClass==true) {
						try {
							Long classId = Long.parseLong(value.substring(1, value.length() - 1));
							ASTNode classNode = ASTUnderConstruction.idToNode.get(classId);
							
							//extract variable name, default value is arbitrary
							String identity = "*";
							String type = classNode.getProperty("type");
							//System.err.println("class value: "+classId+" "+type);
							switch(type) {
							//function parameter
							//TODO: add class to AST_PARAM
							case "AST_PARAM":
								Long paramList = PHPCSVEdgeInterpreter.child2parent.get(classId);
								Long funcList = PHPCSVEdgeInterpreter.child2parent.get(paramList);
								
								int paramId;
								for(paramId=0; paramId<PHPCSVEdgeInterpreter.parent2child.get(paramList).size(); paramId++) {
									//find the location of parameter
									//System.err.println("ParamList: "+PHPCSVEdgeInterpreter.parent2child.get(paramList).get(paramId)+" "+classId);
									if(PHPCSVEdgeInterpreter.parent2child.get(paramList).get(paramId).equals(classId)) {
										//System.err.println("Param Id: "+paramId);
										break;
									}
								}
								//get the current function name
								Long funcId = PHPCSVEdgeInterpreter.child2parent.get(paramList);
								ASTNode funcNode = ASTUnderConstruction.idToNode.get(funcId);
								identity = funcNode.getEscapedCodeStr();
								identity = identity+"()"+"~"+paramId;
								//check if it is a method or function
								if(ASTUnderConstruction.idToNode.get(funcList).getProperty("type").equals("AST_METHOD")) {
									String className = funcNode.getEnclosingClass();
									String namespace = funcNode.getEnclosingNamespace();
									Long classNodeId = PHPCGFactory.getClassId(className, funcId, namespace);
									identity = classNodeId+"::"+identity;
								}
								System.err.println("Param identity: "+id+" "+identity);
								break;
							//variable
							case "AST_VAR":
								Long varName = PHPCSVEdgeInterpreter.parent2child.get(classId).get(0);
								identity = ASTUnderConstruction.idToNode.get(varName).getEscapedCodeStr();
								//it is not a global variable, and we cannot parse it value
								if(!PHPCGFactory.globalMap.containsKey(identity)) {
									identity = "*";
									break;
								}
								System.err.println("Variable identity: "+id+" "+identity);
								break;
							//class property $var->prop
							case "AST_PROP":
								//get property name
								Long propId = PHPCSVEdgeInterpreter.parent2child.get(classId).get(1);
								String propType = ASTUnderConstruction.idToNode.get(propId).getProperty("type");
								while(propType.equals("AST_PROP")) {
									propId = PHPCSVEdgeInterpreter.parent2child.get(propId).get(1);
									propType = ASTUnderConstruction.idToNode.get(propId).getProperty("type");
								}
								if(propType.equals("string")) {
									identity = ASTUnderConstruction.idToNode.get(propId).getEscapedCodeStr();
									//System.err.println("Property name: "+identity);
								}
								else {
									System.err.println("Unsupport property name type: "+classId);
								}
								//get property class
								//TODO support more cases
								String propClass = "-1";
								Long propClassId = PHPCSVEdgeInterpreter.parent2child.get(classId).get(0);
								propType = ASTUnderConstruction.idToNode.get(propClassId).getProperty("type");
								//$this->prop
								if(propType.equals("AST_VAR")) {
									Long var = PHPCSVEdgeInterpreter.parent2child.get(propClassId).get(0);
									ASTNode varNode = ASTUnderConstruction.idToNode.get(var);
									if(varNode.getProperty("type").equals("string")) {
										String name = varNode.getEscapedCodeStr();
										if(name.equals("this")) {
											//System.err.println("This: "+varNode);
											propClass = ASTUnderConstruction.idToNode.get(propClassId).getEnclosingClass();
											String namespace = ASTUnderConstruction.idToNode.get(propClassId).getEnclosingNamespace();
											propClass = PHPCGFactory.getClassId(propClass, varNode.getNodeId(), namespace).toString();
										}
									}
								}
								propClass = propClass+"::";
								identity = propClass+identity;
								System.err.println("Property identity: "+id+" "+identity);
								break;
							//self::pro
							case "AST_STATIC_PROP":
								//get property name
								Long staticPropId = PHPCSVEdgeInterpreter.parent2child.get(classId).get(1);
								String staticPropType = ASTUnderConstruction.idToNode.get(staticPropId).getProperty("type");
								while(staticPropType.equals("AST_PROP")) {
									staticPropId = PHPCSVEdgeInterpreter.parent2child.get(staticPropId).get(1);
									staticPropType = ASTUnderConstruction.idToNode.get(staticPropId).getProperty("type");
								}
								if(staticPropType.equals("string")) {
									identity = ASTUnderConstruction.idToNode.get(staticPropId).getEscapedCodeStr();
									//System.err.println("Property name: "+identity);
								}
								else {
									System.err.println("Unsupport property type: "+classId);
								}
								//get property class
								String staticPropClass = "-1";
								Long staticPropClassId = PHPCSVEdgeInterpreter.parent2child.get(classId).get(0);
								propType = ASTUnderConstruction.idToNode.get(staticPropClassId).getProperty("type");
								//e.g., static::prop
								if(propType.equals("AST_NAME")) {
									Long var = PHPCSVEdgeInterpreter.parent2child.get(staticPropClassId).get(0);
									ASTNode varNode = ASTUnderConstruction.idToNode.get(var);
									String namespace = ASTUnderConstruction.idToNode.get(staticPropClassId).getEnclosingNamespace();
									if(varNode.getProperty("type").equals("string")) {
										String name = varNode.getEscapedCodeStr();
										if(name.equals("self") || name.equals("parent") || name.equals("static")) {
											//System.err.println("This: "+varNode);
											staticPropClass = classNode.getEnclosingClass();
											Long staticId = PHPCGFactory.getClassId(staticPropClass, var, namespace);
											if(name.equals("parent")) {
												staticId = PHPCGFactory.ch2prt.get(staticId).get(0);
											}
											staticPropClass = staticId.toString();
										}
										else {
											staticPropClass = name;
											staticPropClass = PHPCGFactory.getClassId(staticPropClass, var, namespace).toString();
										}
									}
								}
								staticPropClass = staticPropClass+"::";
								identity = staticPropClass+identity;
								System.err.println("Static property identity: "+id+" "+identity);
								break;
							//return from method
							case "AST_METHOD_CALL":
								String methodClass = "-1";
								Long methodClassId = PHPCSVEdgeInterpreter.parent2child.get(classId).get(0);
								//get class of method call
								//TODO: add more cases
								if(ASTUnderConstruction.idToNode.get(methodClassId).getProperty("type").equals("AST_VAR")) {
									Long var = PHPCSVEdgeInterpreter.parent2child.get(methodClassId).get(0);
									ASTNode varNode = ASTUnderConstruction.idToNode.get(var);
									if(varNode.getProperty("type").equals("string")) {
										String name = varNode.getEscapedCodeStr();
										if(name.equals("this")) {
											//System.err.println("This: "+varNode);
											methodClass = ASTUnderConstruction.idToNode.get(methodClassId).getEnclosingClass();
											String namespace = ASTUnderConstruction.idToNode.get(methodClassId).getEnclosingNamespace();
											methodClass = PHPCGFactory.getClassId(methodClass, var, namespace).toString();
										}
									}
								}
								//get method name of method call
								Long methodNameId = PHPCSVEdgeInterpreter.parent2child.get(classId).get(1);
								if(ASTUnderConstruction.idToNode.get(methodNameId).getProperty("type").equals("string")) {
									identity = ASTUnderConstruction.idToNode.get(methodNameId).getEscapedCodeStr();
								}
								else {
									System.err.println("Unsupport method name type: "+classId);
								}
								
								methodClass = methodClass+"::";
								identity = methodClass+identity+"()";
								System.err.println("Method call identity: "+id+" "+identity);
								break;
							//return from static method
							case "AST_STATIC_CALL":
								//get method name of static method call
								Long staticMethodNameId = PHPCSVEdgeInterpreter.parent2child.get(classId).get(1);
								if(ASTUnderConstruction.idToNode.get(staticMethodNameId).getProperty("type").equals("string")) {
									identity = ASTUnderConstruction.idToNode.get(staticMethodNameId).getEscapedCodeStr();
								}
								else {
									System.err.println("Unsupport static method name type: "+classId);
								}
								//get static method's class
								String staticMethodClass = "-1";
								Long staticMethodClassId = PHPCSVEdgeInterpreter.parent2child.get(classId).get(0);
								propType = ASTUnderConstruction.idToNode.get(staticMethodClassId).getProperty("type");
								//e.g., static::prop
								if(propType.equals("AST_NAME")) {
									Long var = PHPCSVEdgeInterpreter.parent2child.get(staticMethodClassId).get(0);
									ASTNode varNode = ASTUnderConstruction.idToNode.get(var);
									if(varNode.getProperty("type").equals("string")) {
										String name = varNode.getEscapedCodeStr();
										String namespace = ASTUnderConstruction.idToNode.get(classId).getEnclosingNamespace();
										//System.err.println();
										if(name.equals("self") || name.equals("parent") || name.equals("static")) {
											System.err.println("This: "+varNode);
											staticMethodClass = ASTUnderConstruction.idToNode.get(classId).getEnclosingClass();
											Long staticClassId = PHPCGFactory.getClassId(staticMethodClass, var, namespace);
											if(name.equals("parent")) {
												System.err.println("parent: "+staticClassId+" "+PHPCGFactory.ch2prt.get(staticClassId));
												staticClassId = PHPCGFactory.ch2prt.get(staticClassId).get(0);
											}
											staticMethodClass = staticClassId.toString();
										}
										else {
											staticMethodClass = name;
											staticMethodClass = PHPCGFactory.getClassId(staticMethodClass, var, namespace).toString();
										}
									}
								}
								identity = staticMethodClass + "::" + identity + "()";
								System.err.println("Static method call identity: "+id+" "+identity);
								break;
							case "AST_CALL":
								Long funId = PHPCSVEdgeInterpreter.parent2child.get(classId).get(0);
								if(ASTUnderConstruction.idToNode.get(funId).getProperty("type").equals("AST_NAME")) {
									Long var = PHPCSVEdgeInterpreter.parent2child.get(funId).get(0);
									ASTNode varNode = ASTUnderConstruction.idToNode.get(var);
									identity = varNode.getEscapedCodeStr();
								}
								else {
									System.err.println("Unsupport call function type: "+id+" "+classId);
								}
								identity = identity+"()";
								System.err.println("Function identity: "+identity);
								break;
							default:
								System.err.println("Unknown source variable types: "+type+" "+id);
							}
							
							//built-in function get_class()
							if(identity.equals("get_class()")) {
								String classname = classNode.getEnclosingClass();
								String namespace = classNode.getEnclosingNamespace();
								classId = PHPCGFactory.getClassId(classname, classId, namespace);
								varValue.add(classId.toString());
								continue;
							}
							
							//get all the related variables that are defined outside the function
							Set<String> related = check(identity);
							for(String rel : related) {
								if(rel.startsWith("@")) {
									rel = rel.substring(1);
									varValue.add(rel);
								}
								//we get the related NodeIds
								else if(rel.startsWith("#")) {
									rel = rel.substring(1);
									Long relId = Long.parseLong(rel);
									//System.err.println("new Identity: "+relId);
									if(!save.contains(relId)) {
										save.add(relId);
										queue.add(relId);
									}
								}
							}
						} catch(Exception e) {
							
						}
					}
					//we think the variable could be any value if it is defined outside the function
					//TODO: improve it using dynamic analysis
					else {
						value = value.replaceAll("\\$[0-9]+\\$", "*");
						varValue.add(value);
					}
				}
			}
			
		}
	}
	
	//identity -> related node id
	private Set<String> check(String identity) {
		Set<String> ret = new HashSet<String>();
		
		
		//it is a class property or a method
		if(identity.contains("::")) {
			int index = identity.indexOf("::");
			System.err.println("check: "+identity.substring(0, index));
			Long classId = Long.parseLong(identity.substring(0, index));
			String rest = identity.substring(index);
			if(classId==-1) {
				identity = rest;
				for(String possibleIdentity: relations.keySet()) {
					if(possibleIdentity.endsWith(rest)) {
						ret.addAll(relations.get(possibleIdentity));
					}
				}
				//cache1.addAll(identity, (List<String>) ret);
				return ret;
			}
			Set<Long> relatedIds = PHPCGFactory.getAllChild(classId);
			relatedIds.addAll(PHPCGFactory.getAllParent(classId));
			relatedIds.add(classId);
			String wildcard = "-1"+rest;
			System.err.println("wildcard: "+wildcard);
			if(relations.containsKey(wildcard)) {
				ret.addAll(relations.get(wildcard));
			}
			for(Long relatedId: relatedIds) {
				String newIdentity = relatedId+rest;
				if(relations.containsKey(newIdentity)) {
					ret.addAll(relations.get(newIdentity));
				}
			}
		}
		//it is a variable or function
		else {
			if(relations.containsKey(identity)) {
				ret = new HashSet<String>(relations.get(identity));
			}
		}
		return ret;
	}



	public Set<String> IntroDataflow(Long varId) {
		
		Set<String> ret = new HashSet<String>();
		Set<String> ret1 = new HashSet<String>();
		involvedIds.add(varId);
		ret1.add("$"+varId.toString()+"$");
		String varName="";
		
		//variables, class properties, static class properties
		if(! (ASTUnderConstruction.idToNode.get(varId) instanceof Variable ||
				ASTUnderConstruction.idToNode.get(varId) instanceof StaticPropertyExpression) ) {
			return ret1;
		}
		
		//get variable name
		long childId = PHPCSVEdgeInterpreter.parent2child.get(varId).get(0);
		ASTNode child = ASTUnderConstruction.idToNode.get(childId);
		//property fetch
		if(child.getProperty("type").equals("AST_VAR")) {
			childId = PHPCSVEdgeInterpreter.parent2child.get(childId).get(0);
			//$obj->var => $obj
			child = ASTUnderConstruction.idToNode.get(childId);
			varName = child.getEscapedCodeStr();
		}
		//static property fetch
		else if(child.getProperty("type").equals("AST_NAME")) {
			//System.err.println(varId);
			if(ASTUnderConstruction.idToNode.get(varId).getProperty("type").equals("AST_CONST")) {
				return ret1;
			}
			//Class::var => Class::var
			String clsName = ((Identifier) child).getNameChild().getEscapedCodeStr();
			String mtdName = ASTUnderConstruction.idToNode.get(PHPCSVEdgeInterpreter.parent2child.get(varId).get(1)).getEscapedCodeStr();
			varName = clsName+"::"+mtdName;
		}
		//variable fetch
		else if(child.getProperty("type").equals("string")) {
			//$var => var
			varName = child.getEscapedCodeStr();
			//$this
			if(varName.equals("this")) {
				String className = ASTUnderConstruction.idToNode.get(varId).getEnclosingClass();
				String namespace = ASTUnderConstruction.idToNode.get(varId).getEnclosingNamespace();
				String classID = PHPCGFactory.getClassId(className, varId, className).toString();
				ret.add(classID);
				return ret;
			}
		}
		else {
			//System.err.println("Unsupport variable name: "+varId);
			return ret1;
		}
		
		//get the statement that variable belongs to.
		while (!DDG.Locate.containsKey(String.valueOf(varId)+"_"+varName)) {
			if(PHPCSVEdgeInterpreter.child2parent.containsKey(varId)) {
				varId = PHPCSVEdgeInterpreter.child2parent.get(varId);
				//get node's type and make sure we stop before AST_STMT_LIST
				String rootType =  ASTUnderConstruction.idToNode.get(varId).getProperty("type");
				if (rootType.equals("AST_STMT_LIST")) {
					return ret1;
				}
			}
			else {
				return ret1;
			}
		}
		
		//get source root node
		Queue<Long> getSourceId = new LinkedList<Long>();
		getSourceId.offer(varId);
		Set<Long> sourceRootId = getSource(getSourceId, varName);
		sourceRootId.remove(varId);
		
		if(sourceRootId.isEmpty()) {
			return ret1;
		}
		
		//System.err.println("Intro Data Flow: "+varId+" "+sourceRootId.toString());
			
		//Parse root statement.
		Iterator<Long> it = sourceRootId.iterator();
		while (it.hasNext()) {
			Long root = it.next();
			Set<String> intro = ParseStatement(root, varName);
			
			//Get the root expression node
			ret.addAll(intro);
	    }
		if(ret.isEmpty()) {
			return ret1;
		}
		return ret;
	}
	
	//get source data from source data's statement.
	private Set<String> ParseStatement(Long Stmtid, String var) {
		String rootType =  ASTUnderConstruction.idToNode.get(Stmtid).getProperty("type");
		ASTNode expNode = new ASTNode();
		Set<String> expValue = new HashSet<String>();
		
		switch (rootType) {
		case "AST_ASSIGN":
		case "AST_ASSIGN_REF":
		case "AST_STATIC":
			expNode = ASTUnderConstruction.idToNode.get(Stmtid).getChild(1);
			if(expNode==null) {
				break;
			}
			expValue = new HashSet<String>(ParseExp(expNode)); 
			//System.err.println("Get value from statement: "+var+" "+expValue.toString());
			break;
		//exit when meet a param.
		case "AST_PARAM":
			if(isClass==true) {
				Long typeId = PHPCSVEdgeInterpreter.parent2child.get(Stmtid).get(0);
				expNode = ASTUnderConstruction.idToNode.get(typeId);
				expValue = new HashSet<String>();
				//get class from param
				if(expNode.getProperty("type").equals("AST_NAME")) {
					String typeName = expNode.getChild(0).getEscapedCodeStr();
					//expValue.add(typeName);
					String namespace = expNode.getEnclosingNamespace();
					Long classId = PHPCGFactory.getClassId(typeName, typeId, namespace);
					//it is not a user-defined class and we ignore it
					if(classId==-1) {
						expValue.add("-2");
						break;
					}
					Set<Long> allChild = PHPCGFactory.getAllChild(classId);
					allChild.add(classId);
					for(Long clsId: allChild) {
						expValue.add(clsId.toString());
					}
					System.err.println("Got class from Param: "+Stmtid+" " + var+" "+expValue);
					involvedIds.add(Stmtid);
				}
				//we try to get class id from comment
				else {
					if(PHPCGFactory.paramCls.containsKey(Stmtid)) {
						Long classId = PHPCGFactory.paramCls.get(Stmtid);
						Set<Long> allChild = PHPCGFactory.getAllChild(classId);
						allChild.add(classId);
						for(Long clsId: allChild) {
							expValue.add(clsId.toString());
						}
						System.err.println("Got class from Param Comment: "+Stmtid+" " + var+" "+expValue);
						involvedIds.add(Stmtid);
					}
				}
			}
			
			break;
			
		case "AST_UNSET":
			expValue.add("-2");
			break;
		default:
			//System.err.println("Unknown root statement type "+Stmtid+" "+rootType);
		}
		//it is not defined within the function
		return expValue;
	}
	
	//evaluate the expression. If we cannot evaluate, then returns the NoteId of the expression
	public LinkedList<String> ParseExp(ASTNode expNode){
		String expType = expNode.getProperty("type");
		LinkedList<String> expValue = new LinkedList<String>();
		Long nodeId;
		
		if(cache2.containsKey(expNode.getNodeId())) {
			expValue = (LinkedList<String>) cache2.get(expNode.getNodeId());
			return expValue;
		}
		
		//analyze different types of exp root type
		switch (expType) {
			case "AST_CONDITIONAL":
				if(expNode.getChild(1)!=null) {
					expValue.addAll(ParseExp(expNode.getChild(1)));
				}
				if(expNode.getChild(2)!=null) {
					expValue.addAll(ParseExp(expNode.getChild(2)));
				}
				break;
			case "AST_MAGIC_CONST":
				String magicFlags = expNode.getFlags();
				switch(magicFlags) {
					case "MAGIC_CLASS":
						expValue.add(expNode.getEnclosingClass());
						break;
					case "MAGIC_FUNCTION":
						expValue.add((((FunctionDef) ASTUnderConstruction.idToNode.get(expNode.getFuncId())).getName()));
						break;
					case "MAGIC_DIR":
						String path = PHPCGFactory.getDir(expNode.getNodeId());
						File A = new File(path);
						File parentFolder = new File(A.getParent());
						try {
							expValue.add(parentFolder.getCanonicalPath());
							break;
						} catch (IOException e1) {
							// TODO Auto-generated catch block
							e1.printStackTrace();
						}
						break;
					case "MAGIC_FILE":
						String path1 = PHPCGFactory.getDir(expNode.getNodeId());
						expValue.add(path1);
						break;
				}
				break;
			case "AST_STATIC_PROP":
			case "AST_PROP":
			case "AST_VAR":
				break;
			case "AST_CONST":
				Identifier constNode = ((Constant)expNode).getIdentifier();
				String constValue = constNode.getNameChild().getEscapedCodeStr();
				if(constValue.equals("null")) {
					expValue.add("");
				}
				else {
					expValue.add(constValue);
				}
				break;
			case "AST_CLASS_CONST":
				String constName = ((ClassConstantExpression) expNode).getConstantName().getEscapedCodeStr();
				//Class:class
				if(constName.equals("class")) {
					Expression constClass = ((ClassConstantExpression) expNode).getClassExpression();
					if(constClass.getProperty("type").equals("AST_NAME")) {
						StringExpression constClassNameNode = ((Identifier) constClass).getNameChild();
						String className = constClassNameNode.getEscapedCodeStr();
						String namespace = expNode.getEnclosingNamespace();
						Long classId = PHPCGFactory.getClassId(className, expNode.getNodeId(), namespace);
						expValue.add(classId.toString());
						System.err.println("Get class from class_const: "+expValue.toString());
					}
				}
				break;
			case "AST_CALL":
				Expression targetFuncNode = ((CallExpressionBase) expNode).getTargetFunc();
				//built-in function get_class() returns the current class
				if(targetFuncNode.getProperty("type").equals("AST_NAME")) {
					StringExpression classNameNode = ((Identifier) targetFuncNode).getNameChild();
					if(classNameNode.getEscapedCodeStr().equals("get_class")) {
						String className = expNode.getEnclosingClass();
						String namespace = expNode.getEnclosingNamespace();
						Long classId = PHPCGFactory.getClassId(className, targetFuncNode.getNodeId(), namespace);
						expValue.add(classId.toString());
						System.err.println("Get class from get_class() "+expValue.toString()+" "+className+" "+namespace);
						break;
					}
				}
				if(expValue.isEmpty()) {
					Long caller=expNode.getNodeId();
					if(PHPCGFactory.call2mtd.containsKey(caller)) {
		        		Set<Long> targetFuncs = new HashSet<Long>(PHPCGFactory.call2mtd.get(caller));
		        		for(Long fun: targetFuncs) {
		        			if(PHPCGFactory.retCls.containsKey(fun)) {
		        				Long classId = PHPCGFactory.retCls.get(fun);
		        				Set<Long> allChild = PHPCGFactory.getAllChild(classId);
		        				allChild.add(classId);
		        				for(Long cls: allChild) {
		        					expValue.add(cls.toString());
		        				}
		        			}
		        		}
		        	}
				}
				break;
			case "AST_STATIC_CALL":
			case "AST_METHOD_CALL":
				Long caller=expNode.getNodeId();
				if(PHPCGFactory.call2mtd.containsKey(caller)) {
	        		Set<Long> targetFuncs = new HashSet<Long>(PHPCGFactory.call2mtd.get(caller));
	        		for(Long fun: targetFuncs) {
	        			if(PHPCGFactory.retCls.containsKey(fun)) {
	        				Long classId = PHPCGFactory.retCls.get(fun);
	        				Set<Long> allChild = PHPCGFactory.getAllChild(classId);
	        				allChild.add(classId);
	        				for(Long cls: allChild) {
	        					expValue.add(cls.toString());
	        				}
	        			}
	        		}
	        	}
				break;
			case "AST_NEW":
				if(isClass==true) {
					//expValue.addAll(ParseExp(expNode.getChild(0)));
					Expression classNode = ((NewExpression) expNode).getTargetClass();
					if(classNode.getProperty("type").equals("AST_NAME")) {
						StringExpression classNameNode = ((Identifier) classNode).getNameChild();
						String className = classNameNode.getEscapedCodeStr();
						//new static(); new self();
						if(className.equals("static") || className.equals("self")) {
							className = expNode.getEnclosingClass();
						}
						String namespace = expNode.getEnclosingNamespace();
						Long classId = PHPCGFactory.getClassId(className, classNode.getNodeId(), namespace);
						if(classId==-1) {
							classId=(long) -2;
						}
						expValue.add(classId.toString());
						System.err.println("Get class from new: "+expValue.toString());
					}
				}
				break;
			case "AST_BINARY_OP":
				if(isClass==false && expNode.getFlags().equals("BINARY_CONCAT")) {
					BinaryOperationExpression newNode = (BinaryOperationExpression) expNode;
					Expression leftStr = newNode.getLeft();
					Expression rightStr = newNode.getRight();
					LinkedList<String> leftStrs = ParseExp(leftStr);
					LinkedList<String> rightStrs = ParseExp(rightStr);
					for(String l: leftStrs) {
						if(l.isEmpty() || (l.charAt(0)>='0'&&l.charAt(0)<='9') || l.charAt(0)=='#') {
							l = "*";
						}
						for(String r: rightStrs) {
							if(r.isEmpty() || (r.charAt(0)>='0'&&r.charAt(0)<='9') || r.charAt(0)=='#') {
								r = "*";
							}
							if(!(l.equals("*") && r.equals("*"))) {
								expValue.add(l+r);
							}
						}
					}
					break;
				}
				break;
			case "AST_NAME_LIST":
				nodeId = expNode.getNodeId();
				for(Long nameId: PHPCSVEdgeInterpreter.parent2child.get(nodeId).values()) {
					expValue.addAll(ParseExp(ASTUnderConstruction.idToNode.get(nameId)));
				}
				break;
			case "AST_CLONE":
				expValue.addAll(ParseExp(expNode.getChild(0)));
				break;
			case "AST_NAME":
				expValue.addAll(ParseExp(expNode.getChild(0)));
				break;
			case "string":
				expValue.add(expNode.getEscapedCodeStr());
				break;
			case "integer":
				expValue.add(expNode.getEscapedCodeStr());
				break;
			case "NULL":
			case "AST_CLOSURE":
			case "UNSET":
				break;
			case "AST_CAST":
				if(isClass==true) {
					expValue.addAll(ParseExp(expNode.getChild(0)));
				}
				break;
		}
		Set<String> tmp = new HashSet<String>();
		tmp.addAll(expValue);
		//cache.put(expNode.getNodeId(), tmp);
		if(expValue.isEmpty()) {
			expValue.add("$"+expNode.getNodeId()+"$");
		}
		cache2.addAll(expNode.getNodeId(), expValue);
		return expValue;
	}
	
	
	//get root node of source statement of root node of variable
	/*
	 * input: variable's root id
	 * output: source root id 
	 */
	protected Set<Long> getSource(Queue<Long> getSourceId, String varName) {
		Set<Long> sourceId = new HashSet<Long>();
		Set<Long> save = new HashSet<Long>();
		Long input = getSourceId.peek();
		
		while(!getSourceId.isEmpty()) {
			Long node = getSourceId.poll();
			if(node>input) {
				continue;
			}
			save.add(node);
			//it is a transition node.
			if(DDG.Locate.containsKey(node.toString()+"_"+varName)) { 
				LinkedList<Long> transitionId = DDG.Locate.get(node.toString()+"_"+varName);
				//add transition nodes to the source node list
				transitionId.forEach((temp) -> {
					if(!save.contains(temp))
						getSourceId.offer(temp);
				});
			}
			//it is a root source node (in the function scope) , add it to return value list.
			else {
				sourceId.add(node);
			}
		}
		return sourceId;
	}
	
	public void reset() {
		varValue.clear();
	}
	
}



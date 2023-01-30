package cg;


import java.io.BufferedReader;
import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
import ast.ASTNode;
import ast.expressions.BinaryOperationExpression;
import ast.expressions.CallExpressionBase;
import ast.expressions.Expression;
import ast.expressions.Identifier;
import ast.expressions.NewExpression;
import ast.expressions.PropertyExpression;
import ast.expressions.StaticPropertyExpression;
import ast.expressions.StringExpression;
import ast.expressions.Variable;
import ast.functionDef.FunctionDefBase;
import ast.functionDef.ParameterList;
import ast.php.declarations.ClassDef;
import ast.php.expressions.ArrayElement;
import ast.php.expressions.ArrayExpression;
import ast.php.expressions.IncludeOrEvalExpression;
import ast.php.expressions.MethodCallExpression;
import ast.php.expressions.StaticCallExpression;
import ast.php.functionDef.Closure;
import ast.php.functionDef.Method;
import ast.php.functionDef.Parameter;
import ast.php.functionDef.FunctionDef;
import ast.php.functionDef.TopLevelFunctionDef;
import inputModules.csv.PHPCSVNodeTypes;
import inputModules.csv.csv2ast.ASTUnderConstruction;
import misc.MultiHashMap;
import tools.php.ast2cpg.PHPCSVEdgeInterpreter;

public class PHPCGFactory {

	// maintains a map of known function names (e.g., "B\foo" -> function foo() in namespace B)
	private static MultiHashMap<String,FunctionDef> functionDefs = new MultiHashMap<String,FunctionDef>();
	// maintains a list of function calls
	private static LinkedList<CallExpressionBase> functionCalls = new LinkedList<CallExpressionBase>();
	
	// maintains a map of known static method names (e.g., "B\A::foo" -> static function foo() in class A in namespace B)
	private static MultiHashMap<String,Method> staticMethodDefs = new MultiHashMap<String,Method>();
	// maintains a list of static method calls
	private static LinkedList<StaticCallExpression> staticMethodCalls = new LinkedList<StaticCallExpression>();
	
	// maintains a map of known constructors (e.g., "B\A" -> static function __construct() in class A in namespace B)
	public static MultiHashMap<String,Method> constructorDefs = new MultiHashMap<String,Method>();
	public static MultiHashMap<String,Method> constructorNameDefs = new MultiHashMap<String,Method>();
	//maintains a map of known destructors
	public static MultiHashMap<String, Method> destructorDefs = new MultiHashMap<String,Method>();
	// maintains a list of static method calls
	private static LinkedList<NewExpression> constructorCalls = new LinkedList<NewExpression>();
	
	//Full name=>methodDef AST node
	private static MultiHashMap<String,Method> nonStaticMethodDefs = new MultiHashMap<String,Method>();
	//method name=>methodDef AST node
	private static MultiHashMap<String,Method> nonStaticMethodNameDefs = new MultiHashMap<String,Method>();
	//maintains a list of non-static method calls
	private static LinkedList<MethodCallExpression> nonStaticMethodCalls = new LinkedList<MethodCallExpression>();
	//resolve variable value
	private static HashMap<String, Long> topLevelFunctionDefs = new HashMap<String, Long>();
	
	//private static ParseVar parsevar = new ParseVar();
	public static HashMap<String, Long> classDef = new HashMap<String, Long>();
	public static MultiHashMap<Long, Long> inhe = new MultiHashMap<Long, Long>();
	public static MultiHashMap<Long, Long> ch2prt = new MultiHashMap<Long, Long>();
	public static MultiHashMap<Long, Long> prt2ch = new MultiHashMap<Long, Long>();
	//MethodDef node id => return classDef node id 
	public static HashMap<Long, Long> ret = new HashMap<Long, Long>();
	public static MultiHashMap<Long, Long> call2mtd = new MultiHashMap<Long, Long>();
	public static MultiHashMap<Long, Long> mtd2call = new MultiHashMap<Long, Long>();
	public static MultiHashMap<Long, Long> mtd2mtd = new MultiHashMap<Long, Long>();
	public static LinkedList<Long> collectAllFun = new LinkedList<Long>();
	public static MultiHashMap<String, Long> globalMap = new MultiHashMap<String, Long>();
	public static Set<Long> func_get_args = new HashSet<Long>();
	public static Set<Long> call_user = new HashSet<Long>();
	private final static Lock lock = new ReentrantLock();
	private final static Lock lockC = new ReentrantLock();
	private final static Lock lockp = new ReentrantLock();
	
	//public static MultiHashMap<Long, Long> parentCall = new MultiHashMap<Long, Long>();
	//public static MultiHashMap<Long, String> collectThis = new MultiHashMap<Long, String>();
	//public static MultiHashMap<Long, String> collectParent = new MultiHashMap<Long, String>();;
	public static Set<Long> topFunIds = new HashSet<Long>();
	//private static MultiHashMap<Long, Long> func2cls = new MultiHashMap<Long, Long>();
	public static Set<Long> magicMtdDefs = new HashSet<Long>();  
	public static Set<String> classUsed = new HashSet<String>();
	public static MultiHashMap<String, Long> fullname2Id = new MultiHashMap<String, Long>();
	public static MultiHashMap<String, Long> name2Id = new MultiHashMap<String, Long>();
	public static int callsiteNumber = 0;
	//public static int unknownCallsite = 0;
	public static Set<Long> unknownIds = new HashSet<Long>();
	//public static HashMap<Long, Set<Long>> cls2Allcls = new HashMap<Long, Set<Long>>();
	public static HashMap<Long, Long> ignoreIds = new HashMap<Long, Long>();
	public static Set<Long> allFuncDef = new HashSet<Long>();
	public static int omit=0;
	public static Set<Long> omitIds = new HashSet<Long>();
	public static HashMap<String, Long> path2TopFile = new HashMap<String, Long>();
	public static Set<String> removed = new HashSet<String>();
	//public static HashMap<Long, String> topIdcache= new HashMap<Long, String>();
	public static MultiHashMap<String, String> filepaths = new MultiHashMap<String, String>();
	public static HashMap<Long, String> id2Name = new HashMap<Long, String>();
	
	//public static Map<Long, Long> howmany = new TreeMap<Long, Long>();
	public static MultiHashMap<Long, String> allUse = new MultiHashMap<Long, String>();
	
	public static Set<String> initial = new HashSet<String>();
	public static Set<Long> suspicious = new HashSet<Long>();
	
	public static Set<Long> Abstract = new TreeSet<Long>();
	
	//public static MultiHashMap<String, FunctionDef> name2Def = new MultiHashMap<String, FunctionDef>();
	
	//public static int entry=0, dependent=0;
	public static Set<Long> removeId = new HashSet<Long>();
	public static int topsum = 0;
	public static Set<Long> condes = new HashSet<Long>();
	public static HashMap<Long, Long> paramCls = new HashMap<Long, Long>();
	public static HashMap<Long, Long> retCls = new HashMap<Long, Long>();
	//public static Set<String> indirect = new HashSet<String>();
	public static HashSet<Long> sinks = new HashSet<Long>();
	public static List<Long> objCaller = new ArrayList<Long>();
	//public static MultiHashMap<Long, Long> file2file = new MultiHashMap<Long, Long>();
	public static MultiHashMap<Long, Long> callee2caller = new MultiHashMap<Long, Long>();
	//public static HashMap<Long, String> caller2path = new HashMap<Long, String>();
	public static HashSet<String> bwlines = new HashSet<String>();
	public static MultiHashMap<String, Long> path2callee = new MultiHashMap<String, Long>();
	public static HashSet<String> entrypoint = new HashSet<String>();
	public static HashSet<Long> allFunc = new HashSet<Long>();
	public static HashSet<Long> allStaticMtd = new HashSet<Long>();
	public static HashSet<Long> allMtd = new HashSet<Long>();
	public static HashSet<Long> allConstructor = new HashSet<Long>();
	
	//public static Set<FunctionDef> constructSet = new HashSet<FunctionDef>();
	/**
	 * Creates a new CG instance based on the lists of known function definitions and function calls.
	 * 
	 * Call this after all function definitions and calls have been added to the lists using
	 * addFunctionDef(FunctionDef) and addFunctionCall(CallExpression).
	 * 
	 * After a call graph has been constructed, these lists are automatically reset.
	 * 
	 * @return A new call graph instance.
	 */
	public static CG newInstance() {
		CG cg = new CG();
		
		init();
		
		//createSpiderEdges(cg);
		System.err.println("@");
		createFunctionCallEdges(cg);
		System.err.println("@@");
		createConstructorCallEdges(cg);
		System.err.println("@@@");
		createStaticMethodCallEdges(cg);
		System.err.println("@@@@");
		createNonStaticMethodCallEdges(cg);
		System.err.println("@@@@@");

		reset(cg);
		
		return cg;
	}

	private static void createSpiderEdges(CG cg) {
		
		File profile = new File("/data/xdebug/wp");
		File[] files = profile.listFiles();
		if (files != null) {
		    for (File file : files) {
		    	try (BufferedReader br = new BufferedReader(new FileReader(file), (int) file.length())) {
		    	    String line;
		    	    while ((line = br.readLine()) != null) {
		    	       //line = line.replaceAll("[^\\x00-\\x7F]", " ");
		    	       String[] words = line.split("\\s+");
		    	       if(words.length!=6) {
		    	    	   continue;
		    	       }
		    	       String iden = words[words.length-1]+words[words.length-2];
		    	       if(bwlines.contains(iden)) {
		    	    	   continue;
		    	       }
		    	       bwlines.add(iden);
		    	       //integrate with results produced by Spider.
		    	       if(words.length==6) {
		    	    	   String target = words[4];
		    	    	   target = target.replace("/var/www/html/", "/home/users/chluo/goal/");
		    	    	   target = target.replace("()", "");
		    	    	   String path = words[5].replace("/var/www/html/", "/home/users/chluo/goal/");
		    	    	   //main functon
		    	    	   if(target.equals("{main}")) {
		    	    		   String entry = path.substring(0, path.indexOf(":"));
		    	    		   entry = "<"+entry+">";
		    	    		   entrypoint.add(entry);
 		    	    	   }
		    	    	   //require or include
		    	    	   if(target.startsWith("include(") || target.startsWith("require(") ||
		    	    			   target.startsWith("require_once(") || target.startsWith("include_once(")) {
		    	    		   target = target.substring(target.indexOf("/"));
		    	    		   target = target.replace(")", "");
		    	    		   //System.out.println("target: "+target);
		    	    		   //we find the included file
		    	    		   if(topLevelFunctionDefs.containsKey(target)) {
		    	    			   Long targetID = topLevelFunctionDefs.get(target);
		    	    			   if(!(path2callee.containsKey(path) && path2callee.get(path).contains(targetID))) {
		    	    				   path2callee.add(path, targetID);
		    	    			   }
		    	    		   }
		    	    	   }
		    	    	   //general function calls
		    	    	   else {
		    	    		   target = target.replace("->", "::");
		    	    		   //System.out.println("className: "+target);
		    	    		   //it is a method
		    	    		   if(target.contains("::")){
		    	    			   String className=target.substring(0, target.indexOf("::"));
		    	    			   String rest=target.substring(target.indexOf("::"));
		    	    			   rest=rest.replace("::__construct", "");
		    	    			   Long classID = getClsId(className, "-1");
		    	    			   String methodkey = classID+rest;
		    	    			   for(String funcKey: constructorDefs.keySet()) {
		    	    				   if(funcKey.equals(methodkey)) {
		    	    						for(FunctionDef func: constructorDefs.get(funcKey)){
		    	    							if(!(path2callee.containsKey(path) && path2callee.get(path).contains(func.getNodeId()))) {
		    	    								path2callee.add(path, func.getNodeId());
		    	    							}
		    	    						}
		    	    					}
		    	    			   }
		    	    			   for(String funcKey: nonStaticMethodDefs.keySet()) {
		    	    				   if(funcKey.equals(methodkey)) {
		    	    						for(FunctionDef func: nonStaticMethodDefs.get(funcKey)){
		    	    							if(!(path2callee.containsKey(path) && path2callee.get(path).contains(func.getNodeId()))) {
		    	    								path2callee.add(path, func.getNodeId());
		    	    							}
		    	    						}
		    	    					}
		    	    			   }
		    	    			   for(String funcKey: staticMethodDefs.keySet()) {
		    	    				   if(funcKey.equals(methodkey)) {
		    	    						for(FunctionDef func: staticMethodDefs.get(funcKey)){
		    	    							if(!(path2callee.containsKey(path) && path2callee.get(path).contains(func.getNodeId()))) {
		    	    								path2callee.add(path, func.getNodeId());
		    	    							}
		    	    						}
		    	    					}
		    	    			   }
		    	    		   }
		    	    		   //it is a function
		    	    		   else {
		    	    			   String functionKey = target;
		    	    			   for(String funcKey: staticMethodDefs.keySet()) {
		    	    				   if(funcKey.equals(functionKey)) {
		    	    						for(FunctionDef func: staticMethodDefs.get(funcKey)){
		    	    							if(!(path2callee.containsKey(path) && path2callee.get(path).contains(func.getNodeId()))) {
		    	    								path2callee.add(path, func.getNodeId());
		    	    							}
		    	    						}
		    	    					}
		    	    			   }
		    	    		   }
		    	    	   }   
		    	    	   //path2callee.add(path, target);
		    	       }
		    	    }
		    	} catch(Exception e) {
		    		
		    	}
		    }
		  } 
		
		System.out.println("pat2callee: "+path2callee.size());
		//require and include
		for(Long ildId: toTopLevelFile.includeLoc) {
			String path = getDir(ildId);
			ASTNode require = ASTUnderConstruction.idToNode.get(ildId);
			path=path+":"+require.getLocation().startLine;
			if(path2callee.containsKey(path)) {
				//one line may call multiple target functions
				//System.out.println("require path "+path);
				call2mtd.addAll(ildId, path2callee.get(path));
				continue;
			}
		}
		
	}

	static void init() {
		setInheritance();
		getComment();
		ParseVar.ParseInterRelationship();
		
		HashSet<Long> save = new HashSet<Long>(topFunIds);
		for(Long topId: save) {
			String path = getDir(topId);
			//we do not consider vendor files
			if(path.contains("/vendor/")) {
				topFunIds.remove(topId);
			}
		}
		
		for(Long nodeid : PHPCSVEdgeInterpreter.collectUse.keySet()) {
			Long topid = toTopLevelFile.getTopLevelId(nodeid);
			allUse.add(topid, PHPCSVEdgeInterpreter.collectUse.get(nodeid));
		}
	
	}
	
	
	private static void getComment() {
		for(Long funcId: allFuncDef) {
			FunctionDef func = (FunctionDef) ASTUnderConstruction.idToNode.get(funcId);
			String namespace = func.getEnclosingNamespace();
			String comment = func.getDocComment();
			if(comment==null || comment.isEmpty()) {
				continue;
			}
			String[] comments = comment.split("\n");
			ParameterList paramList = func.getParameterList();
			HashMap<String, Long> name2Id = new HashMap<String, Long>();
			for(int i=0; i<paramList.size(); i++) {
				Parameter param = (Parameter) paramList.getParameter(i);
				name2Id.put(param.getName(), param.getNodeId());
			}
			
			//parse each comment line
			for(String line: comments) {
				//it is a param line
				if(line.contains("@param")) {
					for(String param: name2Id.keySet()) {
						//this line contains one param name
						if(line.contains('$'+param)) {
							line = line.replace("|", " ");
							String[] words = line.split("\\s+");
							for(String word: words) {
								if(word==null || word.isEmpty()) {
									continue;
								}
								//get the class of param from its comment
								Long classId = getClassId(word, funcId, namespace);
								if(classId!=-1) {
									paramCls.put(name2Id.get(param), classId);
									break;
								}
							}
							//there is no a valid class name
							if(!paramCls.containsKey(name2Id.get(param)) && !line.toLowerCase().contains("mix")) {
								paramCls.put(name2Id.get(param), (long) -2);
							}
						}
				
					}
					
				}
				//it is a return line
				else if(line.contains("@return")) {
					String[] words = line.split("\\s+");
					for(String word: words){
						Long classId = getClassId(word, funcId, namespace);
						if(classId!=-1) {
							retCls.put(funcId, classId);
						}
					}
				}
			}
		}
	}

	public static String getDir(Long astid) {
		Long topId = toTopLevelFile.getTopLevelId(astid);
		//FunctionDef funNode =  (FunctionDef) ASTUnderConstruction.idToNode.get(funId);
		if(!ASTUnderConstruction.idToNode.get(topId).getFlags().equals("TOPLEVEL_FILE")) {
			System.err.println("Fail to find top file for target function "+astid);
			return "";
		}
		TopLevelFunctionDef topFile = (TopLevelFunctionDef) ASTUnderConstruction.idToNode.get(topId);
		String phpPath = topFile.getName();
		phpPath = phpPath.substring(1, phpPath.length()-1);
		phpPath = phpPath.replace("//", "/");
		//topIdcache.put(astid, phpPath);
		return phpPath;
	}
	
	//class inheritance
	private static void setInheritance() {
		for(Long clsId:  inhe.keySet()) {
			Set<Long> prts = getParentClassId(clsId);
			for(Long prt: prts) {
				if(clsId.equals(prt)) {
					continue;
				}
				//System.out.println("cls2prt:"+clsId+" "+prt);
				if(clsId!=-1 && prt!=-1) {
					ch2prt.add(clsId, prt);
					prt2ch.add(prt, clsId);
				}
			}
		}	
	}
	
	public static Set<Long> getAllChild(Long prtId){
		
		Set<Long> cldList = new HashSet<Long>();
		Queue<Long> crtCld = new LinkedList<Long>();
		crtCld.offer(prtId);
		while(!crtCld.isEmpty()) {
			Long crtId = crtCld.poll();
			if(prt2ch.containsKey(crtId)) {
				for(Long ele: prt2ch.get(crtId)) {
					crtCld.add(ele);
					cldList.add(ele);
				}
			}
		}
		
		return cldList;
	}
	
	public static Set<Long> getAllParent(Long childId){
		Set<Long> prtList = new HashSet<Long>();
		Queue<Long> crtPrt = new LinkedList<Long>();
		crtPrt.offer(childId);
		while(!crtPrt.isEmpty()) {
			Long crtId = crtPrt.poll();
			if(ch2prt.containsKey(crtId)) {
				crtPrt.addAll(ch2prt.get(crtId));
				prtList.addAll(ch2prt.get(crtId));
			}
		}
		
		return prtList;
	}

	
	private static void createFunctionCallEdges(CG cg) {
		
		int x1 = functionCalls.size();
		
		AtomicInteger c1= new AtomicInteger(0);
		for(CallExpressionBase functionCall : functionCalls) {
			c1.incrementAndGet();
			System.err.println("function: "+c1+" "+x1);
			
			String path = getDir(functionCall.getNodeId());
			path=path+":"+functionCall.getLocation().startLine;
			if(path2callee.containsKey(path)) {
				//one line may call multiple target functions
				if( functionCall.getTargetFunc() instanceof Identifier) {
					Identifier callIdentifier = (Identifier)functionCall.getTargetFunc();
					if(callIdentifier.getNameChild().getEscapedCodeStr().equals("call_user_func")
						|| callIdentifier.getNameChild().getEscapedCodeStr().equals("call_user_func_array")
						|| callIdentifier.getNameChild().getEscapedCodeStr().equals("spl_autoload_register")
						|| callIdentifier.getNameChild().getEscapedCodeStr().equals("spl_autoload_unregister")) {
						call2mtd.addAll(functionCall.getNodeId(), path2callee.get(path));
					}
					else {
						for(Long target: path2callee.get(path)) {
							ASTNode targetFunc = ASTUnderConstruction.idToNode.get(target);
							String funKey = targetFunc.getEscapedCodeStr();
							if(allFunc.contains(target) && callIdentifier.getNameChild().getEscapedCodeStr().equals(funKey)){
								call2mtd.add(functionCall.getNodeId(), target);
							}
						}
					}
				}
				else {
					for(Long target: path2callee.get(path)) {
						if(allFunc.contains(target)){
							call2mtd.add(functionCall.getNodeId(), target);
						}
					}
				}
				continue;
			}
			
			// make sure the call target is statically known
			if( functionCall.getTargetFunc() instanceof Identifier) {
				
				Identifier callIdentifier = (Identifier)functionCall.getTargetFunc();
				
				// Add the sinks there.
				if(callIdentifier.getNameChild().getEscapedCodeStr().equals("mysql_query") ||
						callIdentifier.getNameChild().getEscapedCodeStr().equals("mysqli_query") ||
						callIdentifier.getNameChild().getEscapedCodeStr().equals("pg_query") ||
						callIdentifier.getNameChild().getEscapedCodeStr().equals("sqlite_query")) {
					sinks.add(functionCall.getNodeId());
				}
				
				if(callIdentifier.getNameChild().getEscapedCodeStr().equals("echo") ||
						callIdentifier.getNameChild().getEscapedCodeStr().equals("print") ||
						callIdentifier.getNameChild().getEscapedCodeStr().equals("print_r") ||
						callIdentifier.getNameChild().getEscapedCodeStr().equals("printf") ||
						callIdentifier.getNameChild().getEscapedCodeStr().equals("exit") ||
						callIdentifier.getNameChild().getEscapedCodeStr().equals("die") ||
						callIdentifier.getNameChild().getEscapedCodeStr().equals("vprintf")) {
					sinks.add(functionCall.getNodeId());
				}
				
			
				if(filterTest(callIdentifier.getNameChild().getEscapedCodeStr())) {
					continue;
				}
				
				//callback in built-in functions
				if(callIdentifier.getNameChild().getEscapedCodeStr().equals("usort") ||
							callIdentifier.getNameChild().getEscapedCodeStr().equals("array_walk")) {
					if(functionCall.getArgumentList().size()<2) {
						continue;
					}
					ASTNode secondArg = functionCall.getArgumentList().getArgument(1);
					//calling method
					if(secondArg.getProperty("type").equals("AST_ARRAY")) {
						String classname = new String();
						String methodname = "";
						ArrayElement classEle = ((ArrayExpression) secondArg).getArrayElement(0);
						ArrayElement methodEle = ((ArrayExpression) secondArg).getArrayElement(1);
						Long clsId = (long) -1;
						if(classEle.getValue().getProperty("type").equals("string")) {
							String namespace = secondArg.getEnclosingNamespace();
							//Long prtId = getClassId(classname, functionCall.getNodeId(), namespace);
							classname = ((StringExpression)(classEle.getValue())).getEscapedCodeStr();
							if(classname.equals("static") || classname.equals("parent") || classname.equals("self")) {
								classname = secondArg.getEnclosingClass(); 
								clsId = getClassId(classname, functionCall.getNodeId(), namespace);
							}
							else {
								clsId = getClassId(classname, functionCall.getNodeId(), namespace);
							}
						}
						else if( classEle.getValue() instanceof Variable
								&& ((Variable)classEle.getValue()).getNameExpression() instanceof StringExpression
								&& ((StringExpression)((Variable)classEle.getValue()).getNameExpression()).getEscapedCodeStr().equals("this")) {
							String namespace = secondArg.getEnclosingNamespace();
							classname = secondArg.getEnclosingClass(); 
							clsId = getClassId(classname, functionCall.getNodeId(), namespace);
						}
						else {
							System.err.println("USORT CLASS: "+functionCall.getNodeId());
						}
						
						if(methodEle.getValue().getProperty("type").equals("string")) {
							methodname = (((StringExpression)(methodEle.getValue())).getEscapedCodeStr());
						}
						else {
							System.err.println("USORT METHOD: "+methodEle.getValue().getProperty("type"));
						}
						
						if(methodname==null) {
							System.err.println("NULL"+functionCall.getNodeId());
						}
						if(clsId!=-1 && !methodname.isEmpty()) {
							System.err.println("USORT: "+functionCall.getNodeId());
							String methodKey = clsId+"::"+methodname;
							addCallEdgeIfDefinitionKnown(cg, nonStaticMethodDefs, functionCall, methodKey, false);
						}
					}
					else {
						System.err.println("Unknown USORT: "+functionCall.getNodeId());
					}
				}
				
				else if(callIdentifier.getNameChild().getEscapedCodeStr().equals("call_user_func")
						|| callIdentifier.getNameChild().getEscapedCodeStr().equals("call_user_func_array")
						|| callIdentifier.getNameChild().getEscapedCodeStr().equals("spl_autoload_register")
						|| callIdentifier.getNameChild().getEscapedCodeStr().equals("spl_autoload_unregister")) {
					//System.err.println(functionCall);
					callsiteNumber++;
					//comparing argument numbers does not apply here
					call_user.add(functionCall.getNodeId());
					
					if(functionCall.getArgumentList().size()==0) {
						continue;
					}
					
					ASTNode firstArg = functionCall.getArgumentList().getArgument(0);
					//System.err.println("CALL_USER: "+firstArg.getProperty("type"));
					
					//call_user_func calls method
					if(firstArg.getProperty("type").equals("AST_ARRAY")) {
						String classname = new String();
						Set<String> methodname = new HashSet<String>();
						Set<Long> clds = new HashSet<Long>();
						
						ArrayElement classEle = ((ArrayExpression) firstArg).getArrayElement(0);
						ArrayElement methodEle = ((ArrayExpression) firstArg).getArrayElement(1);
						
						//System.err.println("CALL_USER_METHOD: "+classEle.getValue().getProperty("type")+" "+methodEle.getValue().getProperty("type"));
						
						if(classEle.getValue().getProperty("type").equals("string")) {
							String namespace = firstArg.getEnclosingNamespace();
							classname = ((StringExpression)(classEle.getValue())).getEscapedCodeStr();
							if(classname.equals("static") || classname.equals("parent") || classname.equals("self")) {
								classname = firstArg.getEnclosingClass(); 
								Long prtId = getClassId(classname, functionCall.getNodeId(), namespace);
								clds.add(prtId);
							}
							else {
								Long clsId = getClassId(classname, functionCall.getNodeId(), namespace);
								clds.add(clsId);
							}
						}
						else if( classEle.getValue() instanceof Variable
								&& ((Variable)classEle.getValue()).getNameExpression() instanceof StringExpression
								&& ((StringExpression)((Variable)classEle.getValue()).getNameExpression()).getEscapedCodeStr().equals("this")) {
							String namespace = firstArg.getEnclosingNamespace();
							classname = firstArg.getEnclosingClass(); 
							clds.add(getClassId(classname, functionCall.getNodeId(), namespace));
						}
						else if(classEle.getValue() instanceof NewExpression && 
								((NewExpression)classEle.getValue()).getTargetClass() instanceof Identifier) {
							NewExpression classNew = (NewExpression) classEle.getValue();
							Identifier classNode = (Identifier) classNew.getTargetClass();
							String className = classNode.getNameChild().getEscapedCodeStr();
							String namespace = classNode.getEnclosingNamespace();
							clds.add(getClassId(className, functionCall.getNodeId(), namespace));
						}
						else {
							ASTNode classVar = classEle.getValue();
							//System.err.println("class: "+classVar.getNodeId());
							ParseVar parsevar = new ParseVar();
							parsevar.init(classVar.getNodeId(), true, "");
							parsevar.handle();
							Set<String> classValue = parsevar.getVar();
							for(String classvalue: classValue) {
								try {
									System.err.println("Parse Long: "+classVar.getNodeId()+" "+classvalue);
									clds.add(Long.parseLong(classvalue));
								} catch(NumberFormatException nfe) {
									System.err.println("Unknown class NodeId: "+classVar.getNodeId()+" "+classvalue);
								}
							}
							parsevar.reset();
						}
						
						//parse method name
						if(methodEle.getValue().getProperty("type").equals("string")) {
							methodname.add(((StringExpression)(methodEle.getValue())).getEscapedCodeStr());
						}
						else {
							ParseVar parsevar = new ParseVar();
							parsevar.init(methodEle.getValue().getNodeId(), false, "");
							parsevar.handle();
							methodname = parsevar.getVar();
						}
						
						//debug call_user_funnc
						System.err.println("call_user_func "+functionCall.getNodeId()+" "+clds.toString()+" "+methodname.toString());
						
						
						for(Long clsDefId: clds) {
							for(String mtdkey: methodname) {
								String methodKey = clsDefId+"::"+mtdkey;
								addCallEdgeIfDefinitionKnown(cg, nonStaticMethodDefs, functionCall, methodKey, false);
							}	
						}
					}
					
					//call_user_func calls function
					else {
						if(firstArg.getProperty("type").equals("string")) {
							String funcname = ((StringExpression)(firstArg)).getEscapedCodeStr();
							addCallEdgeIfDefinitionKnown(cg, functionDefs, functionCall, funcname, false);
						}
					}
				}
				
				
				// if call identifier is fully qualified,
				// just look for the function's definition right away
				if( callIdentifier.getFlags().contains( PHPCSVNodeTypes.FLAG_NAME_FQ)) {
					String functionKey = callIdentifier.getNameChild().getEscapedCodeStr();
					addCallEdgeIfDefinitionKnown(cg, functionDefs, functionCall, functionKey, false);
				}

				// otherwise, i.e., if the call identifier is not fully qualified,
				// first look in the current namespace, then if the function is not found,
				// look in the global namespace
				// (see http://php.net/manual/en/language.namespaces.rules.php)
				else {
					boolean found = false;
					// note that looking in the current namespace first only makes
					// sense if we are not already in the global namespace anyway
					if( !callIdentifier.getEnclosingNamespace().isEmpty()) {
						String functionKey = callIdentifier.getEnclosingNamespace() + "\\"
								+ callIdentifier.getNameChild().getEscapedCodeStr();
						found = addCallEdgeIfDefinitionKnown(cg, functionDefs, functionCall, functionKey, false);
					}
					
					// we did not find the function or were already in global namespace;
					// try to find the function in the global namespace
					if( !found) {
						String functionKey = callIdentifier.getNameChild().getEscapedCodeStr();
						addCallEdgeIfDefinitionKnown(cg, functionDefs, functionCall, functionKey, false);
					}
				}
			}
			//we don't know the function name
			else {
				ParseVar parsevar = new ParseVar();
				parsevar.init(functionCall.getTargetFunc().getNodeId(), false, "");
				parsevar.handle();
				Set<String> funcValues = parsevar.getVar();
				for(String funName: funcValues) {
					addCallEdgeIfDefinitionKnown(cg, functionDefs, functionCall, funName, false);
					System.err.println("Call variable function: "+functionCall.getNodeId()+" "+funName);
				}
				parsevar.reset();
			}
			//System.err.println("Statically unknown function call at node id " + functionCall.getNodeId() + "!");
		};
	}
	
	private static boolean filterTest(String escapedCodeStr) {
		if(escapedCodeStr != null &&
				(escapedCodeStr.contains("Test") || escapedCodeStr.contains("test"))) {
			return true;
		}
		return false;
	}

	private static void createConstructorCallEdges(CG cg) {
		int x3=constructorCalls.size();
		AtomicInteger c3 = new AtomicInteger(0);
		
		for( NewExpression constructorCall : constructorCalls) {
		//constructorCalls.parallelStream().forEach(constructorCall -> {
			c3.incrementAndGet();
			System.err.println(x3+" "+c3+" "+constructorCall.getNodeId());
			// make sure the call target is statically known
			
			String path = getDir(constructorCall.getNodeId());
			path=path+":"+constructorCall.getLocation().startLine;
			if(path2callee.containsKey(path)) {
				//one line may call multiple target functions
				//System.out.println("construct:" +path);
				for(Long target: path2callee.get(path)) {
					if(allConstructor.contains(target)) {
						call2mtd.add(constructorCall.getNodeId(), target);
					}
				}	
				continue;
			}
			
			if( constructorCall.getTargetClass() instanceof Identifier) {
				
				Identifier classIdentifier = (Identifier)constructorCall.getTargetClass();
				String constructorKey = classIdentifier.getNameChild().getEscapedCodeStr();
				String nameSpace = classIdentifier.getEnclosingNamespace();
				
				//we ignore test files
				if(filterTest(constructorKey) ||
						filterTest(constructorCall.getEnclosingClass()) ||
						filterTest(getDir(constructorCall.getNodeId()))) {
					continue;
				}
				
				// if class identifier is fully qualified,
				// just look for the constructor's definition right away
				if(constructorKey.equals("static")) {
					constructorKey = constructorCall.getEnclosingClass();
					Long prtId = getClassId(constructorKey, constructorCall.getNodeId(), nameSpace);
					Set<Long> clds = getAllChild(prtId);
					clds.add(prtId);
					for(Long cld: clds) {
						addCallEdgeIfDefinitionKnown(cg, constructorDefs, constructorCall, cld.toString(), false);
					}
				}
				else if (constructorKey.equals("parent")) {
					constructorKey = constructorCall.getEnclosingClass();
					Long ClassDefId = getClassId(constructorKey, constructorCall.getNodeId(), nameSpace);
					if(ch2prt.containsKey(ClassDefId)) {
						ClassDefId = ch2prt.get(ClassDefId).get(0);
						addCallEdgeIfDefinitionKnown(cg, constructorDefs, constructorCall, ClassDefId.toString(), false);
					}
				}
				else if (constructorKey.equals("self")) {
					constructorKey = constructorCall.getEnclosingClass();
					Long ClassDefId = getClassId(constructorKey, constructorCall.getNodeId(), nameSpace);
					addCallEdgeIfDefinitionKnown(cg, constructorDefs, constructorCall, ClassDefId.toString(), false);
				}
				else {
					Long classId = getClassId(constructorKey, constructorCall.getNodeId(), "");
					addCallEdgeIfDefinitionKnown(cg, constructorDefs, constructorCall, classId.toString(), false);
					//getMethodCall(cg, constructorCall, classId, "__destruct", false);
				}
			}
			else {
				ParseVar parsevar = new ParseVar();
				parsevar.init(constructorCall.getTargetClass().getNodeId(), false, "");
				parsevar.handle();
				Set<String> classValue = parsevar.getVar();
				if(1191711==constructorCall.getNodeId()) {
					System.out.println(1191711+" "+classValue);
				}
				for(String constructorKey: classValue) {
					addCallEdgeIfDefinitionKnown(cg, constructorNameDefs, constructorCall, constructorKey, false);
				}
				//addCallEdgeIfDefinitionKnown(cg, destructorDefs, constructorCall, constructorKey, false);
			}
		};
	}
	
	private static void getStaticCall(Identifier classIdentifier, String methodname, CG cg, StaticCallExpression staticCall) {
		if( classIdentifier.getFlags().contains( PHPCSVNodeTypes.FLAG_NAME_FQ)) {
			Long classId = getClassId(classIdentifier.getNameChild().getEscapedCodeStr(), staticCall.getNodeId(), "");
			String staticMethodKey = classId + "::" + methodname;
			if(methodname.equals("__construct")) {
				staticMethodKey=classId.toString();
				addCallEdgeIfDefinitionKnown(cg, constructorDefs, staticCall, staticMethodKey, false);
			}
			else {
				addCallEdgeIfDefinitionKnown(cg, staticMethodDefs, staticCall, staticMethodKey, false);
			}
		}
		//parent::method
		else if(classIdentifier.getNameChild().getEscapedCodeStr().equals("parent")) {
			String className = staticCall.getEnclosingClass();
			String nameSpace = classIdentifier.getEnclosingNamespace();
			//get self::class nodeId
		    Long ClassDefId = getClassId(className,  staticCall.getNodeId(), nameSpace);
		    if(ClassDefId != -1 && ch2prt.containsKey(ClassDefId)) {
		    	List<Long> prtIds = ch2prt.get(ClassDefId);
		    	for(Long prtId: prtIds) {
		    		String staticMethodKey = prtId+"::"+methodname;
		    		if(methodname.equals("__construct")) {
						staticMethodKey=prtId.toString();
						addCallEdgeIfDefinitionKnown(cg, constructorDefs, staticCall, staticMethodKey, false);
					}
					else {
						addCallEdgeIfDefinitionKnown(cg, staticMethodDefs, staticCall, staticMethodKey, false);
					}
		    	}
		    }
		}
		//static call
		else if(classIdentifier.getNameChild().getEscapedCodeStr().equals("static")) {
			String className = staticCall.getEnclosingClass();
			String nameSpace = classIdentifier.getEnclosingNamespace();
			Long prtId = getClassId(className, staticCall.getNodeId(), nameSpace);
			Set<Long> clds = getAllChild(prtId);
			clds.add(prtId);
			for(Long cld: clds) {
				String staticMethodKey = cld+"::"+methodname;
				if(methodname.equals("__construct")) {
					staticMethodKey=cld.toString();
					addCallEdgeIfDefinitionKnown(cg, constructorDefs, staticCall, staticMethodKey, false);
				}
				else {
					addCallEdgeIfDefinitionKnown(cg, staticMethodDefs, staticCall, staticMethodKey, false);
				}
			}
		}
		//self::method and className::method
		else {
				String className = classIdentifier.getNameChild().getEscapedCodeStr();
				String nameSpace = classIdentifier.getEnclosingNamespace();
				if (classIdentifier.getNameChild().getEscapedCodeStr().equals("self")) {
			    	className = staticCall.getEnclosingClass();
			    }
				Long ClassDefId = getClassId(className, staticCall.getNodeId(), nameSpace);
				//we expect to get class of statically defined class
				if(ClassDefId==-1) {
					return;
				}
				String staticMethodKey = ClassDefId+"::"+methodname;
				if(methodname.equals("__construct")) {
					staticMethodKey=ClassDefId.toString();
					addCallEdgeIfDefinitionKnown(cg, constructorDefs, staticCall, staticMethodKey, false);
				}
				else {
					addCallEdgeIfDefinitionKnown(cg, staticMethodDefs, staticCall, staticMethodKey, false);
				}
		}
	}
	
	private static void createStaticMethodCallEdges(CG cg) {
		int x2 = staticMethodCalls.size();
		AtomicInteger c2 = new AtomicInteger(0);
		for( StaticCallExpression staticCall : staticMethodCalls) {
		//staticMethodCalls.parallelStream().forEach(staticCall -> {
			c2.incrementAndGet();
			System.err.println(x2+" "+c2+" "+staticCall.getNodeId());
			
			String path = getDir(staticCall.getNodeId());
			path=path+":"+staticCall.getLocation().startLine;
			if(path2callee.containsKey(path)) {
				for(Long target: path2callee.get(path)) {
					if(allStaticMtd.contains(target) || allConstructor.contains(target)) {
						ASTNode targetFunc = ASTUnderConstruction.idToNode.get(target);
						if( staticCall.getTargetFunc() instanceof StringExpression) {
							StringExpression methodName = (StringExpression)staticCall.getTargetFunc();
							String methodKey = methodName.getEscapedCodeStr();
							//the target function has incorrect method name
							if(!methodKey.equals(targetFunc.getEscapedCodeStr())) {
								continue;
							}
						}
						call2mtd.add(staticCall.getNodeId(), target);
					}
					//only parent, self, static call calls non-static method
					else if( staticCall.getTargetClass() instanceof Identifier) {
						Identifier classIdentifier = (Identifier)staticCall.getTargetClass();
						if(classIdentifier.getNameChild().getEscapedCodeStr().equals("parent") ||
								classIdentifier.getNameChild().getEscapedCodeStr().equals("self") ||
								classIdentifier.getNameChild().getEscapedCodeStr().equals("static")) {
							ASTNode targetFunc = ASTUnderConstruction.idToNode.get(target);
							if( staticCall.getTargetFunc() instanceof StringExpression) {
								StringExpression methodName = (StringExpression)staticCall.getTargetFunc();
								String methodKey = methodName.getEscapedCodeStr();
								//the target function has incorrect method name
								if(!methodKey.equals(targetFunc.getEscapedCodeStr())) {
									continue;
								}
							}
							call2mtd.add(staticCall.getNodeId(), target);
						}
					}
							
				}	
				continue;
			}
			
			// make sure the call target is statically known
			if( staticCall.getTargetClass() instanceof Identifier
					&& staticCall.getTargetFunc() instanceof StringExpression) {
				
				Identifier classIdentifier = (Identifier)staticCall.getTargetClass();
				StringExpression methodName = (StringExpression)staticCall.getTargetFunc();
				
				if(filterTest(classIdentifier.getNameChild().getEscapedCodeStr()) ||
						filterTest(staticCall.getEnclosingClass()) ||
						filterTest(getDir(staticCall.getNodeId()))){
					continue;
				}
				
				getStaticCall(classIdentifier, methodName.getEscapedCodeStr(), cg, staticCall);
			}
			//class name is a variable or method name is a variable
			else{
				//method name is a string and class name is a variable
				if(staticCall.getTargetFunc() instanceof StringExpression) {
					
					ParseVar parsevar = new ParseVar();
					parsevar.init(staticCall.getTargetFunc().getNodeId(), false, "");
					parsevar.handle();
					
					for(String classId: parsevar.getVar()) {
						String methodKey = classId+"::"+staticCall.getTargetFunc().getEscapedCodeStr();
						addCallEdgeIfDefinitionKnown(cg, staticMethodDefs, staticCall, methodKey, false);
					}
					parsevar.reset();
				}
				//method name is a variable
				else{
					Set<String> methodnames = getMethodName(staticCall);
					//class name is a string
					if(staticCall.getTargetClass() instanceof Identifier) {
						Identifier classIdentifier = (Identifier)staticCall.getTargetClass();
						for(String methodname: methodnames) {
							getStaticCall(classIdentifier, methodname, cg, staticCall);
						}
					}
					//method name is also a variable
					else{
						ParseVar parsevar = new ParseVar();
						parsevar.init(staticCall.getTargetFunc().getNodeId(), false, "");
						parsevar.handle();
						for(String classId: parsevar.getVar()) {
							for(String methodname: methodnames) {
								String methodKey = classId+"::"+methodname;
								addCallEdgeIfDefinitionKnown(cg, staticMethodDefs, staticCall, methodKey, false);
							}
						}
						parsevar.reset();
					}
				}
			}
		};
	}
	
	//given the method name, we get the target method
	private static void withMethodKey(CG cg, MethodCallExpression callsite, String methodkey) {
		//the object is a variable
		if(callsite.getTargetObject() instanceof Variable
				|| callsite.getTargetFunc() instanceof PropertyExpression
				|| callsite.getTargetFunc() instanceof StaticPropertyExpression){
			Expression classVar = callsite.getTargetObject();
			long varId = classVar.getNodeId();
			ParseVar parsevar = new ParseVar();
			parsevar.init(varId, true, "");
			parsevar.handle();
			Set<String> classValues = parsevar.getVar();
			
			for(String classValue: classValues) {
				try {
					Long ClassDefId = Long.parseLong(classValue);
					String methodKey = ClassDefId+"::"+methodkey;
					addCallEdgeIfDefinitionKnown(cg, nonStaticMethodDefs, callsite, methodKey, false);
				}
				catch( Exception e ) {
			        //System.err.println("!"+callsite.getNodeId());
				}
				
			}
			parsevar.reset();
		}
		//new class->method
		else if(callsite.getTargetObject() instanceof NewExpression) {
			NewExpression classNew = (NewExpression) callsite.getTargetObject();
			if(classNew.getTargetClass() instanceof Identifier) {
				Identifier classNode = (Identifier) classNew.getTargetClass();
				String className = classNode.getNameChild().getEscapedCodeStr();
				String namespace = classNode.getEnclosingNamespace();
				Long ClassDefId = getClassId(className, callsite.getNodeId(), namespace);
				String methodKey = ClassDefId+"::"+methodkey;
				addCallEdgeIfDefinitionKnown(cg, nonStaticMethodDefs, callsite, methodKey, false);
			}
		}
		//the object is returned from a function
		else if(callsite.getTargetObject() instanceof CallExpressionBase) {
			objCaller.add(callsite.getNodeId());
		}
		//We don't parse variables with strange representation 
		else { 
			System.err.println("Unsopported method call: "+callsite.getNodeId());
			//System.err.println("Unknown methoddCall type at node id "+methodCall.getNodeId());
		}
	}
	
	private static void createNonStaticMethodCallEdges(CG cg) {
		int x4=nonStaticMethodCalls.size(), x5=0;
		AtomicInteger c4 = new AtomicInteger(0);
		for(MethodCallExpression methodCall: nonStaticMethodCalls) {
		//nonStaticMethodCalls.parallelStream().forEach(methodCall -> {
			c4.getAndIncrement();
			System.err.println(x4+" "+c4+" "+methodCall.getNodeId());
			
			String path = getDir(methodCall.getNodeId());
			path=path+":"+methodCall.getLocation().startLine;
			if(path2callee.containsKey(path)) {
				//one line may call multiple target functions
				x5++;
				for(Long target: path2callee.get(path)) {
					if(allStaticMtd.contains(target) || allMtd.contains(target) || allConstructor.contains(target)) {
						ASTNode targetFunc = ASTUnderConstruction.idToNode.get(target);
						if( methodCall.getTargetFunc() instanceof StringExpression) {
							StringExpression methodName = (StringExpression)methodCall.getTargetFunc();
							String methodKey = methodName.getEscapedCodeStr();
							//the target function has incorrect method name
							if(!methodKey.equals(targetFunc.getEscapedCodeStr())) {
								continue;
							}
						}
						call2mtd.add(methodCall.getNodeId(), target);
					}
				}	
				continue;
			}
			
			if(filterTest(methodCall.getEnclosingClass()) ||
					filterTest(getDir(methodCall.getNodeId()))) {
				continue;
			}
			
			//method name is a string
			if( methodCall.getTargetFunc() instanceof StringExpression) {
				StringExpression methodName = (StringExpression)methodCall.getTargetFunc();
				String methodKey = methodName.getEscapedCodeStr();
				// let's count the dynamic methods
				if( nonStaticMethodNameDefs.containsKey(methodKey)) {
					// check whether there is only one matching function definition
					if( nonStaticMethodNameDefs.get(methodKey).size() == 1) {
						lock.lock();
				        try {
				        	addCallEdge(cg, methodCall, nonStaticMethodNameDefs.get(methodKey).get(0), true);
				        } finally {
				            lock.unlock();
				        }
					}
					else {
						//override methods
						List<Method> allMatch = nonStaticMethodNameDefs.get(methodKey);
						Method first = allMatch.get(0);
						Long firstClass = getClassId(first.getEnclosingClass(), first.getNodeId(), first.getEnclosingNamespace());
						boolean flag = true;
						for(Method candidate: allMatch) {
							Long crtClass = getClassId(candidate.getEnclosingClass(), candidate.getNodeId(), candidate.getEnclosingNamespace());
							//they are methods from different classes 
							if(!(getAllChild(firstClass).contains(crtClass) 
									|| getAllChild(crtClass).contains(firstClass))) {
								flag = false;
								break;
							}
						}
						//they are override methods
						if(flag==true) {
							for(Method candidate: allMatch) {
								lock.lock();
						        try {
						        	addCallEdge(cg, methodCall, candidate, true);
						        } finally {
						            lock.unlock();
						        }
							}
							continue;
						}
						
						//$this->method()
						if( methodCall.getTargetObject() instanceof Variable
							&& ((Variable)methodCall.getTargetObject()).getNameExpression() instanceof StringExpression
							&& ((StringExpression)((Variable)methodCall.getTargetObject()).getNameExpression()).getEscapedCodeStr().equals("this")) {
							
							String enclosingClass = methodCall.getEnclosingClass();
							String nameSpace = methodCall.getEnclosingNamespace();
							Long ClassDefId = getClassId(enclosingClass, methodCall.getNodeId(), nameSpace);
							
							String methodkey = ClassDefId+"::"+methodKey;
							addCallEdgeIfDefinitionKnown(cg, nonStaticMethodDefs, methodCall, methodkey, false);
						}
						//$var->method()
						else {
							withMethodKey(cg, methodCall, methodKey);
						}
					}
					
				}
			}
			
			//$var->$name
			else {
				Set<Long> ClassDefId = new HashSet<Long>();
				Set<String> methodname = new HashSet<String>();
				//Set<Long> classId = new HashSet<Long>();
				
				//we first get class name(if we can get it)
				if( methodCall.getTargetObject() instanceof Variable
						&& ((Variable)methodCall.getTargetObject()).getNameExpression() instanceof StringExpression
						&& ((StringExpression)((Variable)methodCall.getTargetObject()).getNameExpression()).getEscapedCodeStr().equals("this")) {
					String enclosingClass = methodCall.getEnclosingClass();
					String nameSpace = methodCall.getEnclosingNamespace();
					ClassDefId.add(getClassId(enclosingClass, methodCall.getNodeId(), nameSpace));
				}
				else if(methodCall.getTargetObject() instanceof NewExpression && 
						((NewExpression) methodCall.getTargetObject()).getTargetClass() instanceof Identifier) {
					NewExpression classNew = (NewExpression) methodCall.getTargetObject();
					Identifier classNode = (Identifier) classNew.getTargetClass();
					String className = classNode.getNameChild().getEscapedCodeStr();
					String namespace = classNode.getEnclosingNamespace();
					ClassDefId.add(getClassId(className, methodCall.getNodeId(), namespace));
				}
				else if(methodCall.getTargetObject() instanceof Variable ||
						methodCall.getTargetObject() instanceof PropertyExpression ||
						methodCall.getTargetObject() instanceof StaticPropertyExpression){
					ASTNode classVar = methodCall.getTargetObject();
					ParseVar parsevar = new ParseVar();
					parsevar.init(classVar.getNodeId(), true, "");
					parsevar.handle();
					Set<String> classValue = parsevar.getVar();
					//System.err.println(classValue);
					for(String classvalue: classValue) {
						try {
							ClassDefId.add(Long.parseLong(classvalue));
						}catch(NumberFormatException e) {
							
						}
					}
					parsevar.reset();
				}
				else {
					ClassDefId.add((long) -1);
				}
				
				methodname = getMethodName(methodCall);
				
				for(Long clsDefId: ClassDefId) {
					for(String mtdname: methodname) {
						String methodKey = clsDefId+"::"+mtdname;
						addCallEdgeIfDefinitionKnown(cg, nonStaticMethodDefs, methodCall, methodKey, false);
					}
				}
				
				//System.err.println("Statically unknown non-static method call at node id " + methodCall.getNodeId());
			}
			
		};
		
		System.out.println("x5: "+x5);
		
		Collections.sort(objCaller);
		Collections.reverse(objCaller);
		for(Long callsiteID: objCaller) {
			MethodCallExpression callsite = (MethodCallExpression) ASTUnderConstruction.idToNode.get(callsiteID);
			//obj variable
			Long caller = callsite.getTargetObject().getNodeId();
			//methodname
			StringExpression methodName = (StringExpression) (callsite.getTargetFunc());
			String methodKey = methodName.getEscapedCodeStr();
			
			lock.lock();
	        try {
	        	if(call2mtd.containsKey(caller)) {
	        		Set<Long> targetFuncs = new HashSet<Long>(call2mtd.get(caller));
	        		for(Long fun: targetFuncs) {
	        			if(retCls.containsKey(fun)) {
	        				Long classId = retCls.get(fun);
	        				Set<Long> allChild = PHPCGFactory.getAllChild(classId);
	    					allChild.add(classId);
	    					for(Long clsId: allChild) {
	    						methodKey = clsId+"::"+methodKey;
		        				addCallEdgeIfDefinitionKnown(cg, nonStaticMethodDefs, callsite, methodKey, false);
	    					}
	        			}
	        		}
	        	}
	        } finally {
	            lock.unlock();
	        }
		}
	}
	
	private static Set<String> getMethodName(CallExpressionBase callsite){
		Set<String> ret = new HashSet<String>();
		//we try to get method name
		if(callsite.getTargetFunc() instanceof BinaryOperationExpression) {
			BinaryOperationExpression methodNameNode = (BinaryOperationExpression) callsite.getTargetFunc();
			ParseVar parsevar = new ParseVar();
			parsevar.init(1, false, "");
			LinkedList<String> methodNameStrs = parsevar.ParseExp(methodNameNode);
			for(String methodNameStr: methodNameStrs) {
				methodNameStr = methodNameStr.replaceAll("\\$[0-9]+\\$", "*");
				ret.add(methodNameStr);
			}
			parsevar.reset();
		}
		else {
			ParseVar parsevar = new ParseVar();
			parsevar.init(callsite.getTargetFunc().getNodeId(), false, "");
			parsevar.handle();
			Set<String> methodNameStrs = parsevar.getVar();
			for(String methodNameStr: methodNameStrs) {
				ret.add(methodNameStr);
			}
			parsevar.reset();
		}
		return ret;
	}
	
	/**
	 * Checks whether a given function key is known and if yes,
	 * adds a corresponding edge in the given call graph.
	 * 
	 * @return true if an edge was added, false otherwise
	 */
	private static boolean addCallEdgeIfDefinitionKnown(CG cg, MultiHashMap<String,? extends FunctionDef> defSet, CallExpressionBase functionCall, String functionKey, boolean prt2cld) {
		
		//We cannot get the full name of function call
		if(functionKey.contains("-1::") || functionKey.contains("*")) {
			//suspicious.add(functionCall.getNodeId());
			functionKey = functionKey.replace("*", "");
			//we get nothing from the method/function call
			if(functionKey.equals("-1::") || functionKey.equals("")) {
				//suspicious.add(functionCall.getNodeId());
				return true;
			}
			
			functionKey = functionKey.replace("-1::", "::");
			String functionName = functionKey;
			
			int thre = 0;
			//defSet.keySet().parallelStream().forEach(funcKey ->{
			for(String funcKey: defSet.keySet()) {
				
				//candidate
				if(funcKey.contains(functionName) && !funcKey.equals(functionName)) {
					for(FunctionDef func: defSet.get(funcKey)){
						addCallEdge(cg, functionCall, func, prt2cld);
						thre++;
					}
				}
			}
		}
		//the target function is a method and we get the full name of the method
		else if(functionKey.indexOf("::")>0) {
			String classValue = functionKey.substring(0, functionKey.indexOf("::"));
			//we parse correct class Id
			try {
				Long classId = Long.parseLong(classValue);
				while(true) {
					//we get the target function
					if(defSet.keySet().contains(functionKey)) {
						for(FunctionDef func: defSet.get(functionKey)) {
							addCallEdge(cg, functionCall, func, prt2cld);
						}
						return true;
					}
					//we find the target function via parent class
					if(ch2prt.containsKey(classId)) {
						Long parentId = ch2prt.get(classId).get(0);
						functionKey = functionKey.replace(classId+"::", parentId+"::");
						classId = parentId;
					}
					else {
						return false;
					}
				}
			} catch(Exception e) {
				
			}
		}
		//the target function is a constructor 
		else if(functionCall instanceof NewExpression) {
			//we do not know the constructor name
			if(functionKey.equals("-1")) {
				return true;
			}
			try {
				Long classId = Long.parseLong(functionKey);
				while(true) {
					//we get the target function
					if(defSet.keySet().contains(functionKey)) {
						for(FunctionDef func: defSet.get(functionKey)) {
							addCallEdge(cg, functionCall, func, prt2cld);
						}
						return true;
					}
					//we find the target function via parent class
					if(ch2prt.containsKey(classId)) {
						Long parentId = ch2prt.get(classId).get(0);
						functionKey = parentId.toString();
						classId = parentId;
					}
					else {
						return false;
					}
				}
			} catch(Exception e) {
				
			}
		}
		//the target function is a function and we get the full name of the function
		else if(defSet.keySet().contains(functionKey)) {
			for(FunctionDef func: defSet.get(functionKey)) {
				addCallEdge(cg, functionCall, func, prt2cld);
			}
			return true;
		}
		
		return false;
	}
	
	/**
	 * Adds an edge to a given call graph.
	 * 
	 * @return true if an edge was added, false otherwise
	 */
	private static boolean addCallEdge(CG cg, CallExpressionBase functionCall, FunctionDef functionDef, boolean prt2cld) {
		
		//third-party code cannot call first-party code
		if(getDir(functionCall.getNodeId()).contains("vendor")
				&& !getDir(functionDef.getNodeId()).contains("vendor")) {
			return false;
		}
		
		if(filterTest(functionDef.getName()) ||
				filterTest(functionDef.getEnclosingClass()) ||
				filterTest(getDir(functionDef.getNodeId()))) {
			return false;
		}
		
		Long funid = functionCall.getFuncId();
		while(ASTUnderConstruction.idToNode.get(funid) instanceof Closure) {
			funid = ASTUnderConstruction.idToNode.get(funid).getFuncId();
		}
		
		//call site arguments number must bigger than function definition parameter's number
		int callArgSize = functionCall.getArgumentList().size();
		//System.err.println(functionCall);
		int functionDefSize = functionDef.getParameterList().size();
		
		if(callArgSize>functionDefSize 
				&&!func_get_args.contains(functionDef.getNodeId())
				&&!call_user.contains(functionCall.getNodeId())) {
			return false;
		}
		
		
		if(functionDef instanceof Method && 
				(functionDef.getFlags().contains("MODIFIER_PRIVATE") ||  
						functionDef.getFlags().contains("MODIFIER_PROTECTED"))) {
			String callsiteClassName = functionCall.getEnclosingClass();
			String callsiteNamespace = functionCall.getEnclosingNamespace();
			Long callsiteClassId = getClassId(callsiteClassName, functionCall.getNodeId(), callsiteNamespace);
			
			String mtdDefClassName = ((Method) functionDef).getEnclosingClass();
			String mtdDefNamespace = functionDef.getEnclosingNamespace();
			Long mtdClsId =  getClassId(mtdDefClassName, functionDef.getNodeId(), mtdDefNamespace);
			Set<Long> cldIds = getAllChild(mtdClsId);
			cldIds.add(mtdClsId);
			
			//call a public/private method from a function
			if(callsiteClassId==null) {
				return false;
			}
			//only the methods in the same class could call this method
			else if(functionDef.getFlags().contains("MODIFIER_PRIVATE")) {
				if(!callsiteClassId.equals(mtdClsId)) {
					return false;
				}
			}
			else if(functionDef.getFlags().contains("MODIFIER_PROTECTED")) {
				if(!cldIds.contains(callsiteClassId)) {
					return false;
				}
			}
		}
		
		if(functionCall instanceof StaticCallExpression 
				&& ((StaticCallExpression)functionCall).getTargetClass() instanceof Identifier ) {
			Identifier classname = (Identifier) ((StaticCallExpression)functionCall).getTargetClass();
			if(!classname.getNameChild().getEscapedCodeStr().equals("parent") 
					&& !classname.getNameChild().getEscapedCodeStr().equals("self")
					&& !classname.getNameChild().getEscapedCodeStr().equals("static")) {
				if(!(functionDef instanceof Method && functionDef.getFlags().contains("MODIFIER_STATIC"))){
					return false;
				}
			}
		}
		
		lock.lock();
		try {
			//CGNode caller = new CGNode(functionCall);
			//CGNode callee = new CGNode(functionDef);
			//the caller cannot call it self
			if(functionCall.getFuncId().equals(functionDef.getNodeId())) {
				return true;
			}
			if(!(call2mtd.containsKey(functionCall.getNodeId()) && call2mtd.get(functionCall.getNodeId()).contains(functionDef.getNodeId()))) {
				call2mtd.add(functionCall.getNodeId(), functionDef.getNodeId());
				//file2file.add(toTopLevelFile.getTopLevelId(functionCall.getNodeId()), toTopLevelFile.getTopLevelId(functionDef.getNodeId()));
			}
        } finally {
            lock.unlock();
        }
		
		return true;
	}
	
	private static void reset(CG cg) {
	
		MultiHashMap<Long, Long> save = new MultiHashMap<Long, Long>();
		int i1=-1, i2=-1;
		for(Long caller: call2mtd.keySet()) {
			i1=Math.max(i1, call2mtd.get(caller).size());
			ASTNode callerNode = ASTUnderConstruction.idToNode.get(caller);
			Long callerFileId = toTopLevelFile.getTopLevelId(callerNode.getNodeId());
			String callerFile = ASTUnderConstruction.idToNode.get(callerFileId).getEscapedCodeStr();
			List<Long> callees = call2mtd.get(caller);
			if(callees.size()<2) {
				save.addAll(caller, callees);
				continue;
			}
			//System.err.println("caller: "+caller);
			MultiHashMap<Integer, Long> tmp = new MultiHashMap<Integer, Long>();
			for(Long callee: callees) {
				ASTNode calleeNode = ASTUnderConstruction.idToNode.get(callee);
				Long calleeFileId = toTopLevelFile.getTopLevelId(calleeNode.getNodeId());
				String calleeFile = ASTUnderConstruction.idToNode.get(calleeFileId).getEscapedCodeStr();
				int com = getCommon(callerFile, calleeFile);
				tmp.add(com, callee);
			}
			Set<Integer> keys =tmp.keySet();
			List<Integer> lKeys = new ArrayList<Integer>(keys);
			Collections.reverse(lKeys);
			for(int i=0; i<lKeys.size()&&i<5; i++) {
				Integer close = lKeys.get(i);
				List<Long> target = tmp.get(close);
				//System.err.println("Close: "+close+" "+caller+target);
				save.addAll(caller, target);
			}
		}
		
		call2mtd=save;	
		//System.out.println("reset: "+call2mtd);
		
		for(Long caller: call2mtd.keySet()) {
			i2=Math.max(i2, call2mtd.get(caller).size());
			Long callFunc = ASTUnderConstruction.idToNode.get(caller).getFuncId();
			for(Long mtd: call2mtd.get(caller)) {
				CGNode callerNode = null;
				if(ASTUnderConstruction.idToNode.get(caller) instanceof CallExpressionBase) {
					callerNode = new CGNode((CallExpressionBase) ASTUnderConstruction.idToNode.get(caller));
				}
				else if(ASTUnderConstruction.idToNode.get(caller) instanceof IncludeOrEvalExpression) {
					callerNode = new CGNode((IncludeOrEvalExpression) ASTUnderConstruction.idToNode.get(caller));
				}
				CGNode calleeNode = new CGNode((FunctionDef) ASTUnderConstruction.idToNode.get(mtd));
				mtd2call.add(mtd, caller);
				mtd2mtd.add(callFunc, mtd);
				callee2caller.add(mtd, caller);
				cg.addVertex(callerNode);
				cg.addVertex(calleeNode);
				cg.addEdge(new CGEdge(callerNode, calleeNode));
			}
		}
		
		System.err.println("Maximum: "+i1+" "+i2);
		
		functionDefs.clear();
		functionCalls.clear();
		
		staticMethodDefs.clear();
		staticMethodCalls.clear();
		
		//constructorDefs.clear();
		constructorCalls.clear();
		
		nonStaticMethodDefs.clear();
		nonStaticMethodNameDefs.clear();
		nonStaticMethodCalls.clear();

	}
	
	private static int getCommon(String callerFile, String calleeFile) {
		int ret=0;
		int min=Math.min(callerFile.length(), calleeFile.length());
		for(ret=0; ret<min; ret++) {
			if(callerFile.charAt(ret)!=calleeFile.charAt(ret)) {
				break;
			}
		}
		return ret;
	}

	/**
	 * Adds a new known function definition.
	 * 
	 * @param functionDef A PHP function definition. If a function definition with the same
	 *                    name was previously added, then the new function definition will
	 *                    be used for that name and the old function definition will be returned.
	 * @return If there already exists a PHP function definition with the same name,
	 *         then returns that function definition. Otherwise, returns null. For non-static method
	 *         definitions, always returns null.
	 */
	public static FunctionDef addFunctionDef( FunctionDef functionDef) {
		
		
		allFuncDef.add(functionDef.getNodeId());
		// artificial toplevel functions wrapping toplevel code cannot be called
		if( functionDef instanceof TopLevelFunctionDef) {
			topFunIds.add(functionDef.getNodeId());
			String path = getDir(functionDef.getNodeId());
			topLevelFunctionDefs.put(path, functionDef.getNodeId());
			return null;
		}
			
		// we also ignore closures as they do not have a statically known reference
		else if( functionDef instanceof Closure)
			return null;
		
		// finally, abstract methods cannot be called either
		else if( functionDef instanceof Method
				&& functionDef.getFlags().contains(PHPCSVNodeTypes.FLAG_MODIFIER_ABSTRACT)) {
			Abstract.add(functionDef.getNodeId());
			return null;
		}
		
		
		// it's a static method
		else if( functionDef instanceof Method
				&& functionDef.getFlags().contains(PHPCSVNodeTypes.FLAG_MODIFIER_STATIC)) {
			
			allStaticMtd.add(functionDef.getNodeId());
			// get class Id
			Long classId = getClsId(((Method)functionDef).getEnclosingClass(), functionDef.getEnclosingNamespace());
			if(classId!=-1) {
				String staticMethodKey = classId+"::"+functionDef.getName();
				nonStaticMethodNameDefs.add(((Method)functionDef).getName(), (Method)functionDef);
				staticMethodDefs.add(staticMethodKey, (Method)functionDef);
				nonStaticMethodDefs.add(staticMethodKey, (Method)functionDef);
			}
			return null;
		}
		
		// it's a constructor
		// Note that a PHP constructor cannot be static, so the previous case for static methods evaluates to false;
		// also note that there are two possible constructor names: __construct() (recommended) and ClassName() (legacy)
		else if( functionDef instanceof Method
				&& (functionDef.getName().equals("__construct")
						|| functionDef.getName().equals(((Method)functionDef).getEnclosingClass()))) {
			
			allConstructor.add(functionDef.getNodeId());
			// use A\B\C as key for the unique constructor of a class A\B\C
			Long classId = getClsId(((Method)functionDef).getEnclosingClass(), functionDef.getEnclosingNamespace());
			if(classId!=-1) {
				String constructorKey = classId.toString();
				constructorDefs.add( constructorKey, (Method)functionDef);
			}
			constructorNameDefs.add(((Method)functionDef).getEnclosingClass(), (Method)functionDef);
			
			return null;
		}
		
		// other methods than the above are non-static methods
		else if( functionDef instanceof Method) {
			// use foo as key for a non-static method foo in any class in any namespace;
			// note that the enclosing namespace of a non-static method definition is irrelevant here,
			// as that is usually not known at the call site (neither is the class name, except
			// when the keyword $this is used)
			//System.err.println("Function Def: "+((Method)functionDef).getEnclosingClass()+" "+functionDef.getNodeId());
			allMtd.add(functionDef.getNodeId());
			
			Long classId = getClsId(((Method)functionDef).getEnclosingClass(), functionDef.getEnclosingNamespace());
			if(classId!=-1) {
				String methodKey = classId+"::"+functionDef.getName();
				
				nonStaticMethodNameDefs.add(((Method)functionDef).getName(), (Method)functionDef);
				nonStaticMethodDefs.add( methodKey, (Method)functionDef);
			}
			return null;
		}
		
		// it's a function (i.e., not inside a class)
		else {
			// use A\B\foo as key for a function foo() in namespace \A\B
			allFunc.add(functionDef.getNodeId());
			String functionKey = functionDef.getName();
			if( !functionDef.getEnclosingNamespace().isEmpty())
				functionKey = functionDef.getEnclosingNamespace() + "\\" + functionKey;
			functionDefs.add( functionKey, functionDef);
			return null;
		}		
	}
	
	/**
	 * Adds a new function call.
	 * 
	 * @param functionCall A PHP function/method/constructor call. An arbitrary number of
	 *                     distinguished calls to the same function/method/constructor can
	 *                     be added.
	 */
	public static boolean addFunctionCall( CallExpressionBase callExpression) {
		
		// Note: we cannot access any of the CallExpression's getter methods here
		// because this method is called from the PHPCSVNodeInterpreter at the point
		// where it constructs the CallExpression. That is, this method is called for each
		// CallExpression *immediately* after its construction. At that point, the PHPCSVNodeInterpreter
		// has not called the CallExpression's setter methods  (as it has not yet interpreted the
		// corresponding CSV lines).
		// Hence, we only store the references to the CallExpression objects themselves.
	
		callsiteNumber++;
		if( callExpression instanceof StaticCallExpression)
			return staticMethodCalls.add( (StaticCallExpression)callExpression);
		else if( callExpression instanceof NewExpression)
			return constructorCalls.add( (NewExpression)callExpression);
		else if( callExpression instanceof MethodCallExpression) {
			if(nonStaticMethodCalls.isEmpty()) {
				nonStaticMethodCalls.add((MethodCallExpression)callExpression);
				return true;
			}
			MethodCallExpression save = nonStaticMethodCalls.getLast();
			Long lastId = nonStaticMethodCalls.getLast().getNodeId();
			if(lastId+1==callExpression.getNodeId()) {
				nonStaticMethodCalls.removeLast();
				nonStaticMethodCalls.add((MethodCallExpression) callExpression);
				nonStaticMethodCalls.add(save);
			}
			else {
				nonStaticMethodCalls.add((MethodCallExpression)callExpression);
			}
			return true;
		}
		else
			return functionCalls.add(callExpression);
	}
	
	//we do not analyze the alias;
	
	public static Long getClsId(String className, String nameSpace) {
		Long classId = (long) -1;
		String fullName = nameSpace + "\\" + className;
		for(String clsDef: classDef.keySet()) {
			if(clsDef.equals(fullName)) {
				classId = classDef.get(clsDef);
				return classId;
			}
		}
		for(String clsDef: classDef.keySet()) {
			if(clsDef.equals(className)) {
				classId = classDef.get(clsDef);
				return classId;
			}
		}
		return classId;
	}
	
	//From class name to its classId
	
	public static Long getClassId(String className, Long callSiteId, String nameSpace) {
		if(className.equals("-1")) {
			className = ASTUnderConstruction.idToNode.get(callSiteId).getEnclosingClass();
			nameSpace = ASTUnderConstruction.idToNode.get(callSiteId).getEnclosingNamespace();
		}
		Long classId = (long) -1;
		HashMap<String, String> alias;
		//LinkedList<String> inclusion = Inclusion.getInclusion(toTopLevelFile.getTopLevelId(callSiteId));
		lockC.lock();
        try {
        	alias = Inclusion.getAliasMap(toTopLevelFile.getTopLevelId(callSiteId));
        } finally {
            lockC.unlock();
        }
        String fullName = nameSpace + "\\" + className;
		String aliaName = "-1";
		
		//use ... as ...
		if(alias.containsKey(className)) {
			aliaName = alias.get(className) ;
		}
		
		//no namespace
		if(nameSpace==null || nameSpace.equals("")){
			fullName = className;
		}
		
		//first check alias name
		for(String clsDef: classDef.keySet()) {
			if(clsDef.equals(aliaName)) {
				//System.err.println(clsDef);
				classId = classDef.get(clsDef);
				return classId;
			}
		}
		
		//then full name
		for(String clsDef: classDef.keySet()) {
			if(clsDef.equals(fullName)) {
				classId = classDef.get(clsDef);
				return classId;
			}
		}
		
		//finally, the className may be full qualified.
		for(String clsDef: classDef.keySet()) {
			if(clsDef.equals(className)) {
				classId = classDef.get(clsDef);
				return classId;
			}
		}
		
		return classId;
	}
	
	private static Set<Long> getParentClassId(Long ClassId){
		Set<Long> prtIds = new HashSet<Long>();
		//LinkedList<String> inclusion = Inclusion.getInclusion(toTopLevelFile.getTopLevelId(ClassId));
		ClassDef classNode = (ClassDef) ASTUnderConstruction.idToNode.get(ClassId);
		String namespace = classNode.getEnclosingNamespace();
		
		List<Long> prtNodes = inhe.get(ClassId); 
		for(Long prt: prtNodes) {
			//get inheritance name
			Identifier prtNode = (Identifier) ASTUnderConstruction.idToNode.get(prt);
			String prtClass = prtNode.getNameChild().getEscapedCodeStr();
			Long prtId = getClassId(prtClass, prt, namespace);
			if(prtId!=-1) {
				prtIds.add(prtId);
			}
		}
		
		return prtIds;
	}
	
}








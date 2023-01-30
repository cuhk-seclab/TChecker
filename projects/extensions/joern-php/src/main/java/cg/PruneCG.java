package cg;

import java.io.File;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;

import ast.expressions.Expression;
import ast.expressions.Identifier;
import ast.php.expressions.IncludeOrEvalExpression;
import inputModules.csv.csv2ast.ASTUnderConstruction;
import misc.MultiHashMap;
import tools.php.ast2cpg.CommandLineInterface;

public class PruneCG {
	public static MultiHashMap<Long, String> includeFile = new MultiHashMap<Long, String>();
	public static MultiHashMap<Long, String> includePartialFile = new MultiHashMap<Long, String>();
	public static Set<Long> unknowInclude = new HashSet<Long>();
	//public static MultiHashMap<Long, Long> call2mtd = PHPCGFactory.call2mtd;
	//public static MultiHashMap<Long, Long> mtd2mtd = PHPCGFactory.mtd2mtd;
	public static MultiHashMap<Long, Long> mrdFromMtd = new MultiHashMap<Long, Long>();
	public static Set<Long> suspicious = PHPCGFactory.suspicious;
	//fun->file
	public static HashMap<Long, Integer> fileDependency = new HashMap<Long, Integer>();
	public static HashMap<String, Long> file2Id = new HashMap<String, Long>(); 
	public static HashMap<Long, Integer> ancestors = new HashMap<Long, Integer>();
	public static MultiHashMap<Integer, Long> stores = new MultiHashMap<Integer, Long>();
	public static MultiHashMap<Integer, Long> storeFiles = new MultiHashMap<Integer, Long>();
	public static MultiHashMap<Long, Long> cg = PHPCGFactory.mtd2mtd;
	public static MultiHashMap<Long, Long> fp = new MultiHashMap<Long, Long>();
	public static MultiHashMap<Long, Long> filecache = new MultiHashMap<Long, Long>();
	private final static Lock lock = new ReentrantLock();
	private static MultiHashMap<Long, Long> add = new MultiHashMap<Long, Long>();
	public static String base = CommandLineInterface.baseDir;
	public static MultiHashMap<Long, Long> file2mtd = new MultiHashMap<Long, Long>();
	public static HashMap<Long, String> prmt = new HashMap<Long, String>();
	public static MultiHashMap<Long, String> prmts = new MultiHashMap<Long, String>();
	public static MultiHashMap<Long, Long> callcons = new MultiHashMap<Long, Long>();
	public static MultiHashMap<Long, Long> param = new MultiHashMap<Long, Long>();
	public static MultiHashMap<Long, String> pp = new MultiHashMap<Long, String>();
	public static HashMap<Long, String> ns = new HashMap<Long, String>();
	
	public static void handle() {
		/*
		System.err.println("123");
		init();
		System.err.println("@");
		getIncludedFile();
		System.err.println("@@");
		getAllCallFile();
		System.err.println("@@@");
		prune();
		System.err.println("@@@@");
		reconstruct();
		System.err.println("@@@@@");
		*/
		addEdge();
	}
	
	private static int findPrefix(String a, String b) {
		if(a.equals(b)) {
			return a.length();
		}
		else {
			int index = 0;
			for(char c: b.toCharArray()) {
	            if(c != a.charAt(index)) break;
	            index++;
	        }
			return index;
		}
	}
	
	private static void addEdge() {
		
		
		for(Long sus: PHPCGFactory.suspicious) {
			String src = PHPCGFactory.getDir(sus);
			Long func = ASTUnderConstruction.idToNode.get(sus).getFuncId();;
			if(src.endsWith(".phtml")) {
				List<Long> callees = PHPCGFactory.call2mtd.get(sus);
				if(callees==null) {
					continue;
				}
				int longest=-1;
				for(Long callee: callees) {
					String dst = PHPCGFactory.getDir(callee);
					int crt = findPrefix(src, dst);
					if(crt>longest) {
						longest = crt;
					}
				}
				for(Long callee: callees) {
					String dst = PHPCGFactory.getDir(callee);
					int crt = findPrefix(src, dst);
					if(crt==longest) {
						PHPCGFactory.mtd2mtd.add(func, callee);
					}
				}
			}
		}
		
		for(Long sus: PHPCGFactory.suspicious) {
			List<Long> callees = PHPCGFactory.call2mtd.get(sus);
			if(callees==null) {
				continue;
			}
			int limit = 10;
			if(PHPCGFactory.allFuncDef.size()>100000) {
				limit=18;
			}
			if(callees.size()<limit) {
				for(Long callee: callees) {
					Long fun = ASTUnderConstruction.idToNode.get(sus).getFuncId();
					PHPCGFactory.mtd2mtd.add(fun, callee);
				}
			}
		}
		
		
		for(Long mtd: PHPCGFactory.mtd2mtd.keySet()) {
			if(param.containsKey(mtd)) {
				List<Long> params = param.get(mtd);
				for(Long p: params) {
					if(ASTUnderConstruction.idToNode.get(p).getProperty("type").equals("AST_NAME")) {
						Identifier pAst = (Identifier) ASTUnderConstruction.idToNode.get(p);
						String type = pAst.getNameChild().getEscapedCodeStr();
						if(ASTUnderConstruction.idToNode.get(p).getProperty("flags").equals("NAME_FQ")) {
							if(PHPCGFactory.name2Id.containsKey(type)) {
								System.err.println("xxyy "+type);
								PHPCGFactory.mtd2mtd.addAll(mtd, PHPCGFactory.name2Id.get(type));
							}
						}
						else {
							String namespace = ASTUnderConstruction.idToNode.get(p).getEnclosingNamespace();
							HashMap<String, String> alias = Inclusion.getAliasMap(toTopLevelFile.getTopLevelId(p));
							String fullname = "";
							if(alias.containsKey(type)) {
								fullname = alias.get(type) ;
							}
							else {
								fullname = namespace + "\\" + type;
							}
							if(PHPCGFactory.name2Id.containsKey(fullname)) {
								System.err.println("xxyy "+fullname);
								PHPCGFactory.mtd2mtd.addAll(mtd, PHPCGFactory.name2Id.get(fullname));
							}
						}
					}
				}
			}
		}
		
		cg = PHPCGFactory.mtd2mtd;
		
		for(Long mtd: PHPCGFactory.mtd2mtd.keySet()) {
			Long toplevelId = toTopLevelFile.getTopLevelId(mtd);
			for(Long callee: PHPCGFactory.mtd2mtd.get(mtd)) {
				if(file2mtd.containsKey(toplevelId)
						&&file2mtd.get(toplevelId).contains(callee)) {
					continue;
				}
				file2mtd.add(toplevelId, callee);
			}
		}
		
		for(Long id: prmt.keySet()) {
			Long file = toTopLevelFile.getTopLevelId(id);
			String nameSpace = ASTUnderConstruction.idToNode.get(file).getEnclosingNamespace();
			ns.put(file, nameSpace);
			prmts.add(file, prmt.get(id));
		}
		
		for(Long file: prmts.keySet()) {
			List<String> cmts = prmts.get(file);
			for(String cmt: cmts) {
				if(!cmt.contains("\\")) {
					continue;
				}
				cmt = cmt.replace("\n", "");
				String[] cs = cmt.split("\\s+");
				for(String c: cs) {
					if(c.startsWith("\\")) {
						c = c.substring(1);
						HashMap<String, String> alias = Inclusion.getAliasMap(file);
						//String fullname = "";
						if(alias.containsKey(c)) {
							c = alias.get(c) ;
						}
						else {
							
						}
						if(PHPCGFactory.name2Id.containsKey(c)) {
							for(Long id: PHPCGFactory.name2Id.get(c)) {
								file2mtd.add(file, id);
								callcons.add(file, id);
							}
							break;
						}
						else {
							if(PHPCGFactory.id2Name.values().contains(c)) {
								if(!(pp.containsKey(file)
										&&pp.get(file).contains(c))) {
									pp.add(file, c);
									break;
								}
							}
						}
					}
				}
			}
		}
		
		for(Long topId : PHPCGFactory.topFunIds) {
			Long topFileId = toTopLevelFile.getTopLevelId(topId);
			String filePath = PHPCGFactory.getDir(topFileId);
			file2Id.put(filePath, topFileId);
			HashMap<String, String> alias = Inclusion.getAliasMap(topId);
			Collection<String> use = alias.values();
			for(String cls: use) {
				if(PHPCGFactory.name2Id.containsKey(cls)) {
					for(Long id: PHPCGFactory.name2Id.get(cls)) {
						file2mtd.add(topId, id);
						callcons.add(topId, id);
					}
					break;
				}
			}
 		}
		getIncludedFile();
		for(Long file: includeFile.keySet()) {
			List<String> paths = includeFile.get(file);
			for(String path1: paths) {
				if(path1.startsWith("/")) {
					File A = new File(path1);
					try {
						String path2 = A.getCanonicalPath();
						Long fileId = file2Id.get(path2);
						if(fileId==null) {
							System.err.println("wrong path: "+path2+" "+file);
						}
						else{
							file2mtd.add(file, fileId);
							callcons.add(file, fileId);
						}
					} catch (IOException e) {
						e.printStackTrace();
					}
				}
			}
		}
		
		for(Long file: includePartialFile.keySet()){
			List<String> paths = includePartialFile.get(file);
			for(String path1: paths) {
				for (String file1: file2Id.keySet()) {
					if(file1.contains(path1)) {
						Long fileId = file2Id.get(file1);
						file2mtd.add(file, fileId);
						callcons.add(file, fileId);
					}
				}
			}
		}
		
		for(Long sus: PHPCGFactory.suspicious) {
			Long fun = ASTUnderConstruction.idToNode.get(sus).getFuncId();
			Long toplevelId = toTopLevelFile.getTopLevelId(sus);
			boolean flag = false;
			List<Long> callees = file2mtd.get(toplevelId);
			if(callees==null) {
				continue;
			}
			String crt = PHPCGFactory.getDir(fun);
			File A = new File(crt);
			String Dir = A.getParent();
			for(Long callee: callees) {
				if(callee==null) {
					continue;
				}
				String path = PHPCGFactory.getDir(callee);
				//String Dir = path;
				if(!PHPCGFactory.call2mtd.containsKey(sus)) {
					continue;
				}
				for(Long candidates: PHPCGFactory.call2mtd.get(sus)) {
					if(candidates==null) {
						continue;
					}
					String path1 = PHPCGFactory.getDir(candidates);
					if(path1.equals(path)) {
						flag = true;
						add.add(fun, candidates);
					}
					else {
						String cls = PHPCGFactory.id2Name.get(candidates);
						if(pp.containsKey(toplevelId)&&pp.get(toplevelId).contains(cls)) {
							add.add(fun, candidates);
						}
					}
				}
			}
			/*
			if(flag == false) {
				if(!PHPCGFactory.call2mtd.containsKey(sus)) {
					continue;
				}
				for(Long candidates: PHPCGFactory.call2mtd.get(sus)) {
					String path1 = PHPCGFactory.getDir(candidates);
					if(path1.contains("test")) {
						continue;
					}
					add.add(fun, candidates);
				}
			}
			*/
		}
		for(Long a: add.keySet()) {
			cg.addAll(a, add.get(a));
		}

	}

	private static void reconstruct() {
		for(Long caller: PHPCGFactory.call2mtd.keySet()) {
			Long fun = ASTUnderConstruction.idToNode.get(caller).getFuncId();
			for(Long callee: PHPCGFactory.call2mtd.get(caller)) {
				if(fp.containsKey(fun)
						&& fp.get(fun).contains(callee)) {
					//System.err.println("Prune "+fun+" "+callee);
					continue;
				}
				cg.add(fun, callee);
			}
		}
		System.err.println(PHPCGFactory.call2mtd.size()+" SIZE "+cg.size());
	}

	private static void prune() {
		for(Long sus: suspicious) {
			List<Long> callees = PHPCGFactory.call2mtd.get(sus);
			Long fun = ASTUnderConstruction.idToNode.get(sus).getFuncId();
			List<Long> fileIds = storeFiles.get(fileDependency.get(fun));
			if(callees==null || callees.size()<5) {
				//System.err.println("No callee: "+sus);
				continue;
			}
			for(Long callee: callees) {
				if(!fileIds.contains(toTopLevelFile.getTopLevelId(callee))) {
					//call2mtd.get(sus).remove(callee);
					fp.add(fun, callee);
				}
			}
			//call2mtd.get(sus).removeAll(fp);
		}
	}

	public static void init(){
		if(!base.endsWith("/")) {
			base=base+"/";
		}
		for(Long caller: PHPCGFactory.mtd2mtd.keySet()) {
			if(caller==null) {
				continue;
			}
			List<Long> callees = PHPCGFactory.mtd2mtd.get(caller);
			for(Long callee: callees) {
				if(callee==null) {
					continue;
				}
				if(!(mrdFromMtd.containsKey(callee)
						&& mrdFromMtd.get(callee).contains(caller))) {
					mrdFromMtd.add(callee, caller);
				}
			}
		}
		
		int a = 0;
		Long index=new Long(0);
		for(Long sus: suspicious) {
		//suspicious.parallelStream().forEach(sus->{
			System.err.println("sus "+a+ " "+suspicious.size());
			a++;
			Long fun = ASTUnderConstruction.idToNode.get(sus).getFuncId();
			if(ancestors.containsKey(fun)) {
				continue;
			}
			Set<Long> ret = new HashSet<Long>();
			//getAncestor(fun, fun, ret);
			Queue<Long> que = new LinkedList<Long>();
			que.offer(fun);
			ret.add(fun);
			boolean flag = true;
			while(!que.isEmpty() && flag) {
				Long id = que.poll();
				if(!mrdFromMtd.containsKey(id)) {
					continue;
				}
				List<Long> prts = mrdFromMtd.get(id);
				for(Long prt: prts) {
					if(ancestors.containsKey(prt)) {
						for(Long s: stores.get(ancestors.get(prt))) {
							ret.add(s);
							if(que.contains(s)) {
								que.remove(s);
							}
						}
						if(stores.get(ancestors.get(prt)).contains(id)) {
							flag = false;
							break;
						}
					}
				}
				for(Long prt: prts) {
					if(!ret.contains(prt)) {
						que.offer(prt);
						ret.add(prt);
					}
				}
			}
			Integer hashcode = ret.hashCode();
			ancestors.put(fun, hashcode);
			if(!stores.containsKey(hashcode)) {
				for(Long id: ret) {
					//ancestors.add(fun, id);
					stores.add(hashcode, id);
				}
			}
			//System.err.println("ans "+ancestors.get(fun));
		}
		
		for(Long topId : PHPCGFactory.topFunIds) {
			Long topFileId = toTopLevelFile.getTopLevelId(topId);
			String filePath = PHPCGFactory.getDir(topFileId);
			file2Id.put(filePath, topFileId);
		}
	}
	/*
	private static void getAncestor(Long fun, Long crt, Set<Long> ret) {
		if(ancestors.containsKey(crt)) {
			//ret.addAll(ancestors.get(fun));
			for(Long id: stores.get(ancestors.get(crt))){
				ret.add(id);
			}
			if(stores.get(ancestors.get(crt)).contains(fun)) {
				ancestors.put(fun, 1);
			}
			return;
		}
		
		if(ancestors.containsKey(fun)) {
			return;
		}
		
		ret.add(crt);
		if(mrdFromMtd.get(crt)==null) {
			return;
		}
		for(Long prt: mrdFromMtd.get(crt)) {
			if(!ret.contains(prt) && !ancestors.containsKey(fun)) {
				getAncestor(fun, prt, ret);
			}
		}
	}
	*/
	private static void getAllCallFile() {
		MultiHashMap<Long, Long> fileIncluded = new MultiHashMap<Long, Long>();
		for(Long f: file2Id.values()) {
			//check if caller files include some files
			Queue<Long> que = new LinkedList<Long>();
			Set<Long> collect = new HashSet<Long>();
			que.add(f);
			collect.add(f);
			
			while(!que.isEmpty()) {
				Long crt = que.poll();
				//System.err.println(crt);
				if(crt==null) {
					continue;
				}
				Long callerFile = toTopLevelFile.getTopLevelId(crt);
				//resolve included path
				if(includeFile.containsKey(callerFile)) {
					List<String> paths = includeFile.get(callerFile);
					for(String path1: paths) {
						if(path1.startsWith("/")) {
							File A = new File(path1);
							try {
								path1 = A.getCanonicalPath();
								Long fileId = file2Id.get(path1);
								if(fileId==null) {
									System.err.println("wrong path: "+path1+" "+callerFile);
								}
								else if(!collect.contains(fileId)) {
									que.offer(fileId);
									collect.add(fileId);
								}
							} catch (IOException e) {
								// TODO Auto-generated catch block
								e.printStackTrace();
							}
						}
					}
				}
				if(includePartialFile.containsKey(callerFile)) {
					List<String> paths = includePartialFile.get(callerFile);
					for(String path: paths) {
						path = path.replace("./", "");
						path = path.replace("../", "");
						path = path.replace("*", " ");
						String[] partialPath = path.split(" ");
						//string path1 = "";
						if(partialPath.length==0) {
							for (String file: file2Id.keySet()) {
								collect.add(file2Id.get(file));
							}
							break;
						}
						for (String file: file2Id.keySet()) {
							boolean flag=true;
							for(String p: partialPath) {
								if(!file.contains(p)) {
									flag=false;
									break;
								}
							}
							if(flag==true) {
								Long fileId = file2Id.get(file);
								if(!collect.contains(fileId)) {
									que.offer(fileId);
									collect.add(fileId);
								}
							}
						}
					}
				}
			}
			
			for(Long id: collect) {
				fileIncluded.add(f, id);
			}
		}
		
		int i = 0;
		MultiHashMap<Integer, Long> funcs = new MultiHashMap<Integer, Long>();
		for(Long func: ancestors.keySet()) {
			funcs.add((stores.get(ancestors.get(func)).size()), func);
		}
		List<Integer> tmp = new ArrayList<Integer>();
		for(Integer k: funcs.keySet()) {
			tmp.add(k);
		}
		Collections.sort(tmp);
		
		for(Integer k: tmp) {
			for(Long func: funcs.get(k)) {
				System.err.println("ZZZ "+i+" "+k);
				i++;
				//Long func = ASTUnderConstruction.idToNode.get(callsite).getFuncId();
				if(fileDependency.containsKey(func)) {
					continue;
				}
				//List<Long> callers = ancestors.get(func);
				List<Long> callers = stores.get(ancestors.get(func));
				HashMap<Long, Boolean> key = new HashMap<Long, Boolean>();
				//fileDependency.addAll(func, callers);
				for(Long caller: callers) {
					Long file = toTopLevelFile.getTopLevelId(caller);
					for(Long include: fileIncluded.get(file)) {
						/*
						if(!(fileDependency.containsKey(func) && fileDependency.get(func).contains(include))){
							fileDependency.add(func, include);
						}
						*/
						key.put(include, true);
					}
					if(key.keySet().size()==file2Id.size()) {
						break;
					}
				}
				
				int hashcode = key.hashCode();
				if(!storeFiles.containsKey(hashcode)) {
					for(Long id: key.keySet()) {
						storeFiles.add(hashcode, id);
					}
				}
				fileDependency.put(func, hashcode);
			}
		}
	}

	// Get files included by every file, store it in includeFile toplevelFileid->filenames
	static void getIncludedFile(){
		LinkedList<Long> includeStartNodes = toTopLevelFile.includeLoc;
		for(Long includeStartNode: includeStartNodes) {
			IncludeOrEvalExpression startnode = (IncludeOrEvalExpression) ASTUnderConstruction.idToNode.get(includeStartNode);
			Long toplevelId = toTopLevelFile.getTopLevelId(startnode.getNodeId());
			Expression endnode = startnode.getIncludeOrEvalExpression();
			ParseVar par = new ParseVar();
			LinkedList<String> filenames = par.ParseExp(endnode);
			for(String filename: filenames) {
				File r = new File(filename);
				if(r.isFile()) {
					includeFile.add(toplevelId, r.getAbsolutePath());
					continue;
				}
				File a = new File(PHPCGFactory.getDir(includeStartNode));
				File parentFolder = new File(a.getParent());
				File b = new File(parentFolder, filename);
				if(b.isFile()) {
					includeFile.add(toplevelId, b.getAbsolutePath());
				}
				else {
					//String file = filename.replace("*", "");
					String file = filename.replace("../", "");
					file = file.replace("./", "");
					if(file.length()>0) {
						System.err.println("this "+file+" "+filename);
						includePartialFile.add(toplevelId, file);
					}
				}
			}
		}
	}

}


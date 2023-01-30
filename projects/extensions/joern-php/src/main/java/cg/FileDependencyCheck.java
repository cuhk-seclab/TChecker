package cg;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Queue;
import java.util.Set;

import org.json.JSONArray;
import org.json.JSONObject;

import ast.php.functionDef.TopLevelFunctionDef;
import inputModules.csv.csv2ast.ASTUnderConstruction;
import misc.MultiHashMap;
import tools.php.ast2cpg.CommandLineInterface;
import tools.php.ast2cpg.Main;

public class FileDependencyCheck {
	//private String ComposerPath;
	private String callsitePath;
	private String callsiteRelateivePath;
	private String funcDefPath;
	private String baseDir;
	private String vendorDir;
	//private String crtDir;
	private File file;
	public static MultiHashMap<String, String> includeDirs = new MultiHashMap<String, String>();
	public static MultiHashMap<String, String> excludeDirs = new MultiHashMap<String, String>();
	private static HashMap<String, String> composerLoc = new HashMap<String, String>();
	
	FileDependencyCheck(Long callsiteId, Long funDefId) {
		//TODO
		baseDir = CommandLineInterface.baseDir;
		//vendorDir = baseDir + "vendor/";
		
		//includeDirs = new MultiHashMap<String, String>();
		//excludeDirs = new MultiHashMap<String, String>();
		callsitePath = getDir(callsiteId);
		funcDefPath = getDir(funDefId);  
		
		//System.err.println(callsitePath+" "+funcDefPath);
	}
	
	public boolean handle() throws IOException {
		//map composer.json to its file location
		if(composerLoc.isEmpty()) {
			getComposerLoc(baseDir);
			//System.err.println(composerLoc);
		}
		//if callsite is from a package, then the path should contain vendor
		if(callsitePath.contains("/vendor/")) {
			vendorDir = callsitePath.split("/vendor/", 2)[0]+"/vendor/";
			callsiteRelateivePath = callsitePath.split("/vendor/", 2)[1];
			return check3Dependency();
		}
		else {
			//first-party code only reach code that has been installed
			if(funcDefPath.contains("/vendor/")) {
                if(!includeDirs.containsKey(baseDir)) {
                        findDependency(baseDir);
                        includeDirs.add(baseDir, baseDir);
                }
                //System.err.println(includeDirs);
                if(excludeDirs.containsKey(baseDir))
                for(String excludePath: excludeDirs.get(baseDir)) {
                        if(funcDefPath.contains(excludePath)) {
                                return false;
                        }
                }
                for(String loadedpath: includeDirs.get(baseDir)) {
                        //System.err.println(loadedpath);
                        if(funcDefPath.contains(loadedpath) && loadedpath.contains("/vendor/")) {
                                return true;
                        }
                }
			}
			else {
				return true;
			}
		}
		//return true;
		return false;
	}
	
	public List<File> findFilesWithSameName(File root) {
		  List<File> result = new ArrayList<>();
		  //System.err.println("123 "+root.getAbsolutePath());
		  for (File file : root.listFiles()) {
		    if (file.isFile()) {
		      if (file.getName().equals("composer.json")) {
		        result.add(file);
		      }
		      
		    }
		    else
		    	  result.addAll(findFilesWithSameName(file));
		  }

		  return result;
	}
	
	void getComposerLoc(String dir) {
		//List<File> result = new ArrayList<>();
		File base = new File(dir);
		List<File> result = findFilesWithSameName(base);
		for (File file : result) {
			FileReader reader;
			try {
				//System.err.println(file);
				reader = new FileReader(file);
				char[] chars = new char[(int) file.length()];
				reader.read(chars);
				String jsonString = new String(chars);
				if(reader != null){
			        reader.close();
			    }
				if(jsonString.isEmpty()) {
					continue;
				}
				JSONObject jobj = new JSONObject(jsonString);
					
				//System.err.println(crtPath);
				//find loaded path of current Composer.json 
				if(!jobj.has("name")) {
					//System.err.println(file.getAbsolutePath()+" doesn't have a name!!");
					continue;
				}
				String name = jobj.getString("name");
				//System.err.println("@@@ "+name+" "+file.getAbsolutePath());
				composerLoc.put(name, file.getParent()+"/");
				
			} catch (FileNotFoundException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			} catch (IOException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
		 }
	}
	
	
	private boolean check3Dependency() throws IOException {
		if(funcDefPath.isEmpty()) {
			return true;
		}
		String[] path = callsiteRelateivePath.split("/");
		if(path.length<=2) {
			//Composer sub_folder
			return checkComposer();
		}
		
		String dir = "";
		String[] callsite = callsiteRelateivePath.split("/");
		for(int i=callsite.length-1; i>=0; i--) {
			callsite[i]="composer.json";
			String tryPath="";
			for(int j=0; j<=i; j++) {
				tryPath = tryPath+callsite[j]+"/";
			}
			tryPath = vendorDir+tryPath.substring(0, tryPath.length()-1);
			file = new File(tryPath);
			if (file.exists()) {
				//System.err.println("@@ "+tryPath);
				//System.err.println("fail to find composer.json for "+crtPath);
				//break;
				String realDir = "";
				for(int j=0; j<i; j++) {
					realDir = realDir+callsite[j]+"/";
				}
				realDir = vendorDir + realDir;
				//realDir = realDir;
				dir = realDir;
				break;
			}
		}
		if(dir.isEmpty()) {
			//System.err.println(callsitePath);
			String pj = callsiteRelateivePath.split("/")[0];
			String tmp = vendorDir+pj;
			//pathcache.add(callsitePath, tmp);
			//System.err.println(callsitePath);
			if(funcDefPath.contains(tmp)) {
				return true;
			}
			else {
				return false;
			}
		}
		
		if(!includeDirs.containsKey(dir)) {
			//System.err.println(dir);
			findDependency(dir);
			includeDirs.add(dir,  dir);
		}
		if(excludeDirs.containsKey(dir))
		for(String excludePath: excludeDirs.get(dir)) {
			if(funcDefPath.contains(excludePath)) {
				return false;
			}
		}
		for(String loadedpath: includeDirs.get(dir)) {
			if(funcDefPath.contains(loadedpath)) {
				return true;
			}
		}
		return false;
	}
	
	private boolean checkComposer() {
		String[] path = callsiteRelateivePath.split("/");
		if(path.length==1 && path[0].equals("autoload.php")
				|| path.length==2 && path[0].equals("composer")) {
			String loadedpath=vendorDir+"composer";
			if(funcDefPath.contains(loadedpath)) {
				return true;
			}
		}
		else {
			System.err.println("Unknown callsite locateion at "+callsitePath);
			return true;
		}
		return false;
	}
	
	private void findDependency(String dir) throws IOException {
		//ComposerPath = crtDir+"composer.json";
		
		Queue<String> dependency = new LinkedList<String>();
		dependency.offer(dir);
		Set<String> record = new HashSet<String>();
		
		while(!dependency.isEmpty()) {
			String crtDir =  dependency.poll();
			//System.err.println(crtDir);
			record.add(crtDir);
			String crtPath = crtDir+"composer.json";
			file = new File(crtPath);
			if (!file.exists()) {
				//System.err.println("fail to find composer.json for "+crtPath);
				//break;
				includeDirs.add(dir, crtDir);
				continue;
			}
			FileReader reader = new FileReader(file);
			char[] chars = new char[(int) file.length()];
			reader.read(chars);
			String jsonString = new String(chars);
			if(reader != null){
	            reader.close();
	        }
			JSONObject jobj = new JSONObject(jsonString);
			
			//System.err.println(crtPath);
			//find loaded path of current Composer.json 
			if(!jobj.has("autoload")) {
				continue;
			}
			JSONObject autoload = jobj.getJSONObject("autoload");
			for(String key: autoload.keySet()) {
				switch (key) {
					case "classmap":
					case "files":
						JSONArray arr = autoload.getJSONArray(key);
						for(Object loadPath: arr) {
							if(!(loadPath instanceof String)) {
								System.err.println("Unknown classmap/files format");
								break;
							}
							String loadpath = crtDir+(String)loadPath;
							loadpath = reformat(loadpath);
							
							includeDirs.add(dir, loadpath);
						}
						break;
					case "psr-4":
					case "psr-0":
						for(String k1: autoload.getJSONObject(key).keySet()) {
							if(!(autoload.getJSONObject(key).get(k1) instanceof String)) {
								if(autoload.getJSONObject(key).get(k1) instanceof JSONArray) {
									JSONArray arr1 = (JSONArray) autoload.getJSONObject(key).get(k1);
									for(Object loadPath: arr1) {
										if(!(loadPath instanceof String)) {
											System.err.println("Unknown psr-0/psr-4 format");
											break;
										}
										String loadpath = crtDir+(String)loadPath;
										loadpath = reformat(loadpath);
										includeDirs.add(dir, loadpath);
									}
								}
								else {
									System.err.println("Unknown psr-0/psr-4 "+autoload.getJSONObject(key).get(k1));
								}
								break;
							}
							String loadpath = (String) autoload.getJSONObject(key).get(k1);
							loadpath = crtDir+loadpath;
							loadpath = reformat(loadpath);
							includeDirs.add(dir, loadpath);
						}
						break;
					case "exclude-from-classmap":
						JSONArray eldarr = autoload.getJSONArray(key);
						for(Object loadPath: eldarr) {
							if(!(loadPath instanceof String)) {
								System.err.println("Unknown classmap/files format");
								break;
							}
							String loadpath = crtDir+(String)loadPath;
							loadpath = reformat(loadpath);
							excludeDirs.add(dir, loadpath);
						}
						break;
					default:
						System.err.println("Unknown autoload format "+key);
				}
			}
			
			if(!jobj.has("require")) {
				continue;
			}
			//find which projects are required and add them to the queue 
			JSONObject require = jobj.getJSONObject("require");
			for(String key: require.keySet()) {
				if(!composerLoc.containsKey(key)) {
					continue;
					//System.err.println("Fail to find locations of "+key);
				}
				String newDir = composerLoc.get(key);
				if(!record.contains(newDir))
					dependency.offer(newDir);
			}
			
			if(!jobj.has("suggest")) {
				continue;
			}
			JSONObject suggest = jobj.getJSONObject("suggest");
			for(String key: suggest.keySet()) {
				if(!composerLoc.containsKey(key)) {
					continue;
					//System.err.println("Fail to find locations of "+key);
				}
				String newDir = composerLoc.get(key);
				if(!record.contains(newDir))
					dependency.offer(newDir);
			}
		}
		
		if(!includeDirs.containsKey(dir)) {
			includeDirs.add(dir, "-1");
		}
	}
	
	private String reformat(String path) {
		String ret = path;
		ret = ret.replace("./", "");
		ret = ret.replace("//", "/");
		return ret;
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
		return phpPath;
	}
}



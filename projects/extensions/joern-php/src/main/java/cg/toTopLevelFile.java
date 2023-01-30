package cg;

import java.util.HashMap;
import java.util.LinkedList;

import ast.ASTNode;
import inputModules.csv.csv2ast.ASTUnderConstruction;
import tools.php.ast2cpg.PHPCSVEdgeInterpreter;

public class toTopLevelFile {
	//find "use ... as ..." 
	public static LinkedList<Long> useLoc = new LinkedList<Long>();
	//find require, require_once, include, include_once node id 
	public static LinkedList<Long> includeLoc = new LinkedList<Long>();
	private static HashMap<Long, LinkedList<Long>> Top2use = new HashMap<Long, LinkedList<Long>>();
	private static HashMap<Long, LinkedList<Long>> Top2ild = new HashMap<Long, LinkedList<Long>>();
	
	public static LinkedList<Long> getTop2Use(Long topId){
		//we only do it at first time
		if(Top2use.isEmpty()) {
			setTop2Use();
		}
		//this file doesn't use "use ... as ..."
		if(!Top2use.containsKey(topId)) {
			Top2use.put(topId, new LinkedList<Long>());
		}
			
		return Top2use.get(topId);
	}
	
	//Top id to use ... as ... id
	protected static void setTop2Use() {
		for(Long useId: useLoc) {
			Long topId = getTopLevelId(useId);
			if(!Top2use.containsKey(topId)) {
				Top2use.put(topId, new LinkedList<Long>());
			}
			Top2use.get(topId).add(useId);
		}
		
	}
	
	public static LinkedList<Long> getTop2Ild(Long topId){
		//we only do it at first time
		if(Top2ild.isEmpty()) {
			setTop2Ild();
		}
		//this file doesn't use "include"
		if(!Top2ild.containsKey(topId)) {
			Top2ild.put(topId, new LinkedList<Long>());
		}
			
		return Top2ild.get(topId);
	}
	
	//Top id to use ... as ... id
	protected static void setTop2Ild() {
		for(Long ildId: includeLoc) {
			Long topId = getTopLevelId(ildId);
			//System.err.println(topId);
			if(!Top2ild.containsKey(topId)) {
				Top2ild.put(topId, new LinkedList<Long>());
			}
			Top2ild.get(topId).add(ildId);
		}
		
	}
	
	public static Long getTopClass(Long methodDefId) {
		ASTNode topFun = ASTUnderConstruction.idToNode.get(methodDefId);
		 while(topFun.getFlags()=="" || !topFun.getFlags().equals("TOPLEVEL_CLASS")) {
			//System.err.println(id);
			methodDefId = topFun.getFuncId();
			//System.err.println("@"+methodDefId);
			topFun = ASTUnderConstruction.idToNode.get(methodDefId);
		 }
		 
		 //System.err.println("@"+methodDefId);
		 Long ClassDefId = PHPCSVEdgeInterpreter.child2parent.get(methodDefId);
		 //System.err.println("@"+ClassDefId);
		 return ClassDefId;
	}
	
	public static Long getTopLevelId(Long id) {
		 ASTNode topFun = ASTUnderConstruction.idToNode.get(id);
		 while(topFun.getFlags()==null || !topFun.getFlags().equals("TOPLEVEL_FILE")) {
			//System.err.println(id);
			id = topFun.getFuncId();
			//System.err.println(id);
			topFun = ASTUnderConstruction.idToNode.get(id);
		 }
		 return id;
	}
}


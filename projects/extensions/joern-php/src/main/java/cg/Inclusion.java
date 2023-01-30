package cg;

import java.util.HashMap;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.Set;

import ast.expressions.Expression;
import ast.php.expressions.IncludeOrEvalExpression;
import ast.statements.UseElement;
import ast.statements.UseStatement;
import inputModules.csv.csv2ast.ASTUnderConstruction;
import misc.MultiHashMap;

//find which classes are explicitly included by a class.
//analyze keyword "use ... as ..."
public class Inclusion {
	//toplevelId => (alias => full class name)
	public static HashMap<Long, HashMap<String, String>> Alias = new HashMap<Long, HashMap<String, String>>();
	//toplevelId => full (included) class name
	public static HashMap<Long, LinkedList<String>> inclusion = new HashMap<Long, LinkedList<String>>();
	
	public static MultiHashMap<Long, String> useStrings = new MultiHashMap<Long, String>();
	
	public static LinkedList<String> getInclusion(Long topLevelFileId){
		if(!inclusion.containsKey(topLevelFileId)) {
			inclusion.put(topLevelFileId, new LinkedList<String>());
			setInclusionAndAlias(topLevelFileId);
		}
		return inclusion.get(topLevelFileId);
	}
	
	public static HashMap<String, String> getAliasMap(Long topLevelFileId){
		if(!Alias.containsKey(topLevelFileId)) {
			Alias.put(topLevelFileId, new HashMap<String, String>());
			setInclusionAndAlias(topLevelFileId);
		}
		return Alias.get(topLevelFileId);
	}
	
	/*
	 * Find which classes are explicitly included by a file
	 * input:
	 * topLevelId: node id of topLevelFile
	 */
	public static void setInclusionAndAlias(Long topLevelFileId) {
		
		ParseVar variable = new ParseVar();
		
		//iterate each use statement
		for(Long useId: toTopLevelFile.getTop2Use(topLevelFileId)) {
			UseStatement useNode = (UseStatement) ASTUnderConstruction.idToNode.get(useId);
			Iterator<UseElement> it = useNode.iterator();
			//iterate each element of current use statement
			while(it.hasNext()){
				UseElement useElmt = it.next();
				//get name of "use name as ..."
				String name = useElmt.getNamespace().getEscapedCodeStr();
				useStrings.add(topLevelFileId, name);
				//inclusion.get(topLevelFileId).add(name);
				
				//if alias is not null, add alias of "use ... as alias" and map alias to its name
				if (useElmt.getAlias() != null) {
					String alias = useElmt.getAlias().getEscapedCodeStr();
					//inclusion.get(topLevelFileId).add(alias);
					//alias => full name
					//System.err.println(useElmt.getNodeId());
					if(!Alias.containsKey(topLevelFileId)) {
						Alias.put(topLevelFileId, new HashMap<String, String>());
						//setInclusionAndAlias(topLevelFileId);
					}
					Alias.get(topLevelFileId).put(alias, name);
				}
				else {
					String alias = name.substring(name.lastIndexOf("\\") + 1);
					//System.err.println(alias);
					if(!Alias.containsKey(topLevelFileId)) {
						Alias.put(topLevelFileId, new HashMap<String, String>());
						//setInclusionAndAlias(topLevelFileId);
					}
					Alias.get(topLevelFileId).put(alias, name);
				}
			}
			
			/*
			//iterator include, include_once, require, require_once
			for (Long includeId: toTopLevelFile.getTop2Ild(topLevelFileId)) {
				IncludeOrEvalExpression includeNode = (IncludeOrEvalExpression) ASTUnderConstruction.idToNode.get(includeId);
				Expression exp = includeNode.getIncludeOrEvalExpression();
				variable.init(exp.getNodeId());
				Set<String> includeValues =  variable.getVar();
				for (String includeName: includeValues) {
					if(includeName != null) {
						inclusion.get(topLevelFileId).add(includeName);
					}
				}
			}*/
		}
	}
}


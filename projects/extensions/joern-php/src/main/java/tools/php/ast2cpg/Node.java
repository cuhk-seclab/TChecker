package tools.php.ast2cpg;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.Stack;

import misc.MultiHashMap;

public class Node {
	public List<Node> children = null;
	public HashMap<String, Long> inter = new HashMap<String, Long>();
	public Set<Long> intro = new HashSet<Long>();
	public Long astId = null;
	//public Long nodeId = null;
	public Stack<Long> caller = null;
	public Long parent = null;
	
	
	//the id and identity of the AST Node 
	public Node(Long astId, HashMap<String, Long> inter, Set<Long> intro, Stack<Long> caller) {
		//the node ID
		//this.nodeId=nodeId;
		//current stmt ID
		this.astId=astId; //the ASTID of this statement 
		//previous taint state
		this.inter=inter; //the related inter variables identities and where they are assigned
		this.intro=intro; //the related intro statememt within the function
		this.caller=caller; //the caller of the statement, represented using its node ID
		this.children=new ArrayList<>();
		StaticAnalysis.ID2Node.put(astId, this);
	}
	
	public Node (Node node) {
		//this.nodeId=node.nodeId;
		this.astId=node.astId;
		this.inter=node.inter;
		this.intro=node.intro;
		this.caller=node.caller;
		this.children=node.children;
	}
	
	public void addChild(Node child) {
		//children.add(child);
		child.parent=this.astId;
	}
}


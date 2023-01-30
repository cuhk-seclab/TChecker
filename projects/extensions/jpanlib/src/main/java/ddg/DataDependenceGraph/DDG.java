package ddg.DataDependenceGraph;

import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;
import ast.ASTNode;
import misc.MultiHashMap;
import misc.Pair;
import tools.php.ast2cpg.Node;

public class DDG
{

	private Set<DefUseRelation> defUseEdges = new HashSet<DefUseRelation>();
	//find src note with dst node and symbol 
	public static HashMap<String, LinkedList<Long>> Locate = new HashMap<String, LinkedList<Long>>();
	public static MultiHashMap<Long, Pair<Long, String>> rels = new MultiHashMap<Long, Pair<Long, String>>();
	

	public Set<DefUseRelation> getDefUseEdges()
	{
		return defUseEdges;
	}

	public void add(Object srcId, Object dstId, String symbol)
	{
		DefUseRelation statementPair = new DefUseRelation(srcId, dstId, symbol);
		defUseEdges.add(statementPair);
		
		Long tmpSrcId = ((ASTNode) srcId).getNodeId();
		Long tmpDstId = ((ASTNode) dstId).getNodeId();
		rels.add(tmpSrcId, new Pair<Long, String>(tmpDstId, symbol));
		if (Locate.containsKey(tmpDstId.toString()+"_"+symbol)) {
			Locate.get(tmpDstId.toString()+"_"+symbol).add(tmpSrcId);
		}
		else {
			Locate.put(tmpDstId.toString()+"_"+symbol, new LinkedList<Long>() {/**
				 * 
				 */
				private static final long serialVersionUID = 1L;

			{
				add(tmpSrcId);
			}});
		}
		//Locate.put(((ASTNode) dstId).getNodeId().toString()+"_"+symbol, ((ASTNode) srcId).getNodeId());
	};

	/**
	 * Compares the DDG with another DDG and returns a DDGDifference object
	 * telling us which edges need to be added/removed to transform one DDG into
	 * the other.
	 * 
	 * @param other
	 * @return
	 */
	public DDGDifference difference(DDG other)
	{
		DDGDifference retval = new DDGDifference();
		List<DefUseRelation> thisEdges = new LinkedList<DefUseRelation>(
				this.getDefUseEdges());

		Set<DefUseRelation> otherEdges = new HashSet<DefUseRelation>(
				other.getDefUseEdges());

		while (thisEdges.size() > 0)
		{
			DefUseRelation elem = thisEdges.remove(0);
			if (otherEdges.contains(elem))
				otherEdges.remove(elem);
			else
				retval.addRelToRemove(elem);
		}

		for (DefUseRelation elem : otherEdges)
			retval.addRelToAdd(elem);

		return retval;
	}
	
	@Override
	public String toString() {
		
		StringBuilder sb = new StringBuilder();
		
		for( DefUseRelation ddgEdge : this.getDefUseEdges())
			sb.append( ddgEdge).append( "\n");

		return sb.toString();
	}

}

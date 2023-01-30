package outputModules.csv.exporters;

import java.util.Map;

import ast.ASTNode;
import cg.CG;
import cg.CGEdge;
import databaseNodes.EdgeTypes;
import outputModules.common.CGExporter;
import outputModules.common.Writer;
import outputModules.common.WriterCG;

public class CSVCGExporter extends CGExporter {

	@Override
	protected void addCGEdge(CGEdge cgEdge, Map<String, Object> properties) {

		long srcId = Writer.getIdForObject(cgEdge.getSource());
		long dstId = Writer.getIdForObject(cgEdge.getDestination());
		Writer.addEdge(srcId, dstId, properties, EdgeTypes.CALLS);
	}
	
	protected void addMyCGEdge(CGEdge cgEdge, Map<String, Object> properties) {

		long srcId = WriterCG.getIdForObject(cgEdge.getSource());
		long dstId = WriterCG.getIdForObject(cgEdge.getDestination());
		WriterCG.addEdge(srcId, dstId, properties, EdgeTypes.CALLS);
	}

	/**
	 * Simple method that takes a call graph and writes out the edges.
	 */
	public void writeCGEdges(CG cg) {

		for( CGEdge cgEdge : cg.getEdges())	{
		
			Writer.setIdForObject(cgEdge.getSource(), ((ASTNode)cgEdge.getSource().getASTNode()).getNodeId());
			Writer.setIdForObject(cgEdge.getDestination(), ((ASTNode)cgEdge.getDestination().getASTNode()).getNodeId());
			addCGEdge( cgEdge, null);
			
			// call graph
			WriterCG.setIdForObject(cgEdge.getSource(), ((ASTNode)cgEdge.getSource().getASTNode()).getFuncId());
			WriterCG.setIdForObject(cgEdge.getDestination(), ((ASTNode)cgEdge.getDestination().getASTNode()).getNodeId());
			addMyCGEdge( cgEdge, null);
		}
		// clean up
		Writer.reset();
	}
}

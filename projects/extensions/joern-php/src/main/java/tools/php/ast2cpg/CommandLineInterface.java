package tools.php.ast2cpg;

import org.apache.commons.cli.ParseException;

import tools.CommonCommandLineInterface;

public class CommandLineInterface extends CommonCommandLineInterface
{
	String nodeFile;
	String edgeFile;
	public static String baseDir;

	public String getNodeFile()
	{
		return nodeFile;
	}

	public String getEdgeFile()
	{
		return edgeFile;
	}

	public String getBaseDir() {
		return baseDir;
	}

	public void printHelp()
	{
		formatter.printHelp("importer <nodes.csv> <edges.csv> ...", options);
	}

	public void parseCommandLine(String[] args) throws ParseException
	{
		//if (args.length != 2)
		//	throw new RuntimeException("Please supply a node and an edge file");
		if (args.length != 1)
			throw new RuntimeException("Please supply application path");

		cmd = parser.parse(options, args);

		String[] arguments = cmd.getArgs();
		//nodeFile = arguments[0];
		//edgeFile = arguments[1];
		baseDir = arguments[0];
	}

}

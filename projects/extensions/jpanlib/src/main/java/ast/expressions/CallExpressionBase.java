package ast.expressions;

import ast.ASTNodeProperties;

public class CallExpressionBase extends PostfixExpression
{
	private Expression targetFunc = null;
	private ArgumentList argumentList = null;
	
	public Expression getTargetFunc()
	{
		return this.targetFunc;
	}
	
	public void setTargetFunc(Expression targetFunc)
	{
		this.targetFunc = targetFunc;
		super.addChild(targetFunc);
	}
	
	public ArgumentList getArgumentList()
	{
		return this.argumentList;
	}
	
	public void setArgumentList(ArgumentList argumentList)
	{
		this.argumentList = argumentList;
		super.addChild(argumentList);
	}
	
	public String getEnclosingClass() {
		return getProperty(ASTNodeProperties.CLASSNAME);
	}
	
	public void setEnclosingClass(String classname) {
		setProperty(ASTNodeProperties.CLASSNAME, classname);
	}
}

package ast.expressions;

import ast.ASTNodeProperties;

public class Variable extends Expression
{
	private Expression name = null;
	
	public String getEnclosingNamespace() {
		return getProperty(ASTNodeProperties.NAMESPACE);
	}

	public void setEnclosingNamespace(String namespace) {
		setProperty(ASTNodeProperties.NAMESPACE, namespace);
	}
	
	public void setNameExpression(Expression name) {
		this.name = name;
		super.addChild(name);
	}
	
	public Expression getNameExpression() {
		return this.name;
	}
}

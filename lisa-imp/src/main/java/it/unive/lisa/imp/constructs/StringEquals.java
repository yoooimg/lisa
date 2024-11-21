package it.unive.lisa.imp.constructs;

import it.unive.lisa.program.ClassUnit;
import it.unive.lisa.program.SourceCodeLocation;
import it.unive.lisa.program.cfg.CFG;
import it.unive.lisa.program.cfg.CodeLocation;
import it.unive.lisa.program.cfg.CodeMemberDescriptor;
import it.unive.lisa.program.cfg.NativeCFG;
import it.unive.lisa.program.cfg.Parameter;
import it.unive.lisa.program.cfg.statement.Expression;
import it.unive.lisa.program.cfg.statement.PluggableStatement;
import it.unive.lisa.program.cfg.statement.Statement;
import it.unive.lisa.program.cfg.statement.string.Equals;
import it.unive.lisa.program.type.BoolType;
import it.unive.lisa.program.type.StringType;

/**
 * The native construct representing the equals operation. This construct can be
 * invoked on a string variable {@code x} with {@code x.equals(other)}, where
 * {@code other} is the string that will be checked for equality against
 * {@code x}.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public class StringEquals extends NativeCFG {

	/**
	 * Builds the construct.
	 * 
	 * @param location   the location where this construct is defined
	 * @param stringUnit the unit where this construct is defined
	 */
	public StringEquals(
			CodeLocation location,
			ClassUnit stringUnit) {
		super(new CodeMemberDescriptor(location, stringUnit, true, "equals", BoolType.INSTANCE,
				new Parameter(location, "this", StringType.INSTANCE),
				new Parameter(location, "other", StringType.INSTANCE)),
				IMPStringEquals.class);
	}

	/**
	 * An expression modeling the string equals operation. The type of both
	 * operands must be {@link StringType}. The type of this expression is the
	 * {@link BoolType}.
	 * 
	 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
	 */
	public static class IMPStringEquals extends Equals implements PluggableStatement {

		/**
		 * Builds a new instance of this native call, according to the
		 * {@link PluggableStatement} contract.
		 * 
		 * @param cfg      the cfg where the native call happens
		 * @param location the location where the native call happens
		 * @param params   the parameters of the native call
		 * 
		 * @return the newly-built call
		 */
		public static IMPStringEquals build(
				CFG cfg,
				CodeLocation location,
				Expression... params) {
			return new IMPStringEquals(cfg, location, params[0], params[1]);
		}

		@Override
		public void setOriginatingStatement(
				Statement st) {
			originating = st;
		}

		/**
		 * Builds the equals.
		 * 
		 * @param cfg        the {@link CFG} where this operation lies
		 * @param sourceFile the source file name where this operation is
		 *                       defined
		 * @param line       the line number where this operation is defined
		 * @param col        the column where this operation is defined
		 * @param left       the left-hand side of this operation
		 * @param right      the right-hand side of this operation
		 */
		public IMPStringEquals(
				CFG cfg,
				String sourceFile,
				int line,
				int col,
				Expression left,
				Expression right) {
			this(cfg, new SourceCodeLocation(sourceFile, line, col), left, right);
		}

		/**
		 * Builds the equals.
		 * 
		 * @param cfg      the {@link CFG} where this operation lies
		 * @param location the code location where this operation is defined
		 * @param left     the left-hand side of this operation
		 * @param right    the right-hand side of this operation
		 */
		public IMPStringEquals(
				CFG cfg,
				CodeLocation location,
				Expression left,
				Expression right) {
			super(cfg, location, left, right);
		}
	}
}
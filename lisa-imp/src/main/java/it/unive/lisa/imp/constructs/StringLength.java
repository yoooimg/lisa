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
import it.unive.lisa.program.cfg.statement.string.Length;
import it.unive.lisa.program.type.Int32Type;
import it.unive.lisa.program.type.StringType;

/**
 * The native construct representing the length operation. This construct can be
 * invoked on a string variable {@code x} with {@code x.len()}.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public class StringLength extends NativeCFG {

	/**
	 * Builds the construct.
	 * 
	 * @param location   the location where this construct is defined
	 * @param stringUnit the unit where this construct is defined
	 */
	public StringLength(
			CodeLocation location,
			ClassUnit stringUnit) {
		super(new CodeMemberDescriptor(location, stringUnit, true, "len", Int32Type.INSTANCE,
				new Parameter(location, "this", StringType.INSTANCE)),
				IMPStringLength.class);
	}

	/**
	 * An expression modeling the string length operation. The type of the
	 * operand must be {@link StringType}. The type of this expression is the
	 * {@link Int32Type}.
	 * 
	 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
	 */
	public static class IMPStringLength extends Length implements PluggableStatement {

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
		public static IMPStringLength build(
				CFG cfg,
				CodeLocation location,
				Expression... params) {
			return new IMPStringLength(cfg, location, params[0]);
		}

		@Override
		public void setOriginatingStatement(
				Statement st) {
			originating = st;
		}

		/**
		 * Builds the length.
		 * 
		 * @param cfg        the {@link CFG} where this operation lies
		 * @param sourceFile the source file name where this operation is
		 *                       defined
		 * @param line       the line number where this operation is defined
		 * @param col        the column where this operation is defined
		 * @param parameter  the operand of this operation
		 */
		public IMPStringLength(
				CFG cfg,
				String sourceFile,
				int line,
				int col,
				Expression parameter) {
			this(cfg, new SourceCodeLocation(sourceFile, line, col), parameter);
		}

		/**
		 * Builds the length.
		 * 
		 * @param cfg       the {@link CFG} where this operation lies
		 * @param location  the code location where this operation is defined
		 * @param parameter the operand of this operation
		 */
		public IMPStringLength(
				CFG cfg,
				CodeLocation location,
				Expression parameter) {
			super(cfg, location, parameter);
		}
	}
}
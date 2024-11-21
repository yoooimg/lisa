package it.unive.lisa.checks.warnings;

import it.unive.lisa.program.cfg.CodeMemberDescriptor;
import org.apache.commons.lang3.StringUtils;

/**
 * A warning reported by LiSA on the descriptor of one of the CFGs under
 * analysis.
 * 
 * @author <a href="mailto:luca.negrini@unive.it">Luca Negrini</a>
 */
public class CFGDescriptorWarning extends WarningWithLocation {

	/**
	 * The descriptor where this warning was reported on
	 */
	private final CodeMemberDescriptor descriptor;

	/**
	 * Builds the warning.
	 * 
	 * @param descriptor the descriptor where this warning was reported on
	 * @param message    the message of this warning
	 */
	public CFGDescriptorWarning(
			CodeMemberDescriptor descriptor,
			String message) {
		super(descriptor.getLocation(), message);
		this.descriptor = descriptor;
	}

	/**
	 * Yields the cfg where this warning was reported on.
	 * 
	 * @return the column, or {@code -1}
	 */
	public CodeMemberDescriptor getDescriptor() {
		return descriptor;
	}

	@Override
	public int compareTo(
			Warning o) {
		int cmp;
		if ((cmp = super.compareTo(o)) != 0)
			return cmp;

		if (!(o instanceof CFGDescriptorWarning))
			return getClass().getName().compareTo(o.getClass().getName());

		CFGDescriptorWarning other = (CFGDescriptorWarning) o;
		if ((cmp = StringUtils.compare(descriptor.toString(), other.descriptor.toString())) != 0)
			return cmp;

		return 0;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = super.hashCode();
		result = prime * result + ((descriptor == null) ? 0 : descriptor.hashCode());
		return result;
	}

	@Override
	public boolean equals(
			Object obj) {
		if (this == obj)
			return true;
		if (!super.equals(obj))
			return false;
		if (getClass() != obj.getClass())
			return false;
		CFGDescriptorWarning other = (CFGDescriptorWarning) obj;
		if (descriptor == null) {
			if (other.descriptor != null)
				return false;
		} else if (!descriptor.equals(other.descriptor))
			return false;
		return true;
	}

	@Override
	public String getTag() {
		return "DESCRIPTOR";
	}

	@Override
	public String toString() {
		return getLocationWithBrackets() + " on '" + descriptor.getFullSignatureWithParNames() + "': "
				+ getTaggedMessage();
	}
}

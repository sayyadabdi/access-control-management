package ac;

import java.util.HashMap;
import java.util.Random;

import core.IPermissionRequest;
import core.PermissionRequestDecision;
import core.UserConsent;
import permission.Permission;

public class AccessControlManager implements IPermissionRequest
{
	private HashMap<process.Process, Permission> procPermMap = new HashMap<>();

	@Override
	public PermissionRequestDecision ask(process.Process proc, Permission perm)
	{
		PermissionRequestDecision decision = makeDecision(proc, perm);

		if (decision == PermissionRequestDecision.GRANT)
			procPermMap.put(proc, perm);

		return decision;
	}

	public void arbitraryAction()
	{
		// Do nothing for now.
	}

	private PermissionRequestDecision makeDecision(process.Process proc,
			Permission perm)
	{
		if (new Random().nextBoolean())
		{
			return askUserPermission(proc, perm) == UserConsent.ALLOW
					? PermissionRequestDecision.GRANT
					: PermissionRequestDecision.DENY;
		}
		else
		{
			return ArbitraryDecision(perm);
		}
	}

	private UserConsent askUserPermission(process.Process proc, Permission perm)
	{
		return new Random().nextBoolean() ? UserConsent.ALLOW
				: UserConsent.REJECT;
	}

	private PermissionRequestDecision ArbitraryDecision(Permission perm)
	{
		// e.g., decision based on permission groups.
		return new Random().nextBoolean() ? PermissionRequestDecision.GRANT
				: PermissionRequestDecision.DENY;
	}
}

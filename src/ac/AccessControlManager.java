package ac;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Random;

import core.IPermissionRequest;
import core.PermissionRequestDecision;
import core.UserConsent;
import permission.Permission;

public class AccessControlManager implements IPermissionRequest
{
	private HashMap<process.Process, List<Permission>> procPermMap = new HashMap<>();

	private HashMap<Permission, List<process.Process>> allowedProcs = new HashMap<>();

	@Override
	public PermissionRequestDecision ask(process.Process proc, Permission perm)
	{
		if (procPermMap.get(proc) == null)
			procPermMap.put(proc, new ArrayList<>());

		List<Permission> list = procPermMap.get(proc);
		if (list.contains(perm))
			return PermissionRequestDecision.GRANT;

		PermissionRequestDecision decision = makeDecision(proc, perm);

		if (allowedProcs.get(perm) == null)
			allowedProcs.put(perm, new ArrayList<>());

		if (decision == PermissionRequestDecision.GRANT)
		{
			list.add(perm);

			if (!allowedProcs.get(perm).contains(proc))
				allowedProcs.get(perm).add(proc);
		}
		else
		{
			if (allowedProcs.get(perm).contains(proc))
				allowedProcs.get(perm).remove(proc);
		}

		return decision;
	}

	public void uninstallApplication(process.Process proc)
	{
		incompleteRevoke();

		for (Permission p : allowedProcs.keySet())
		{
			List<process.Process> list = allowedProcs.get(p);
			if (list != null && list.contains(proc))
				list.remove(proc);
		}
	}

	public void arbitraryAction()
	{
		// Do nothing for now.
	}

	public void incompleteRevoke()
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

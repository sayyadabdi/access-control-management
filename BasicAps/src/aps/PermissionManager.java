package aps;

import java.util.HashMap;
import java.util.Map;
import java.util.Random;

import entities.Application;
import entities.Permission;
import enums.ConsentType;

public class PermissionManager
{

	// Custom permissions (CPs) are unique unless packages are signed with the
	// same certificate.
	// The CP's definer should already be installed.

	private static PermissionManager instance;

	private final Map<Application, Integer> installedApplications = new HashMap<>();

	private final Map<Application, Map<Permission, ConsentType>> appPerms = new HashMap<>();

	private PermissionManager()
	{
	}

	public ConsentType requestPermission(Application app, Permission perm)
	{
		if (!installedApplications.containsKey(app))
			return ConsentType.DENIED;

		if (getPermission(app, perm) != null)
			return getPermission(app, perm);

		switch (perm.type)
		{
		case NORMAL:
		{
			if (app.manifest.permissions.contains(perm))
				setPermission(app, perm, ConsentType.ALLOWED);
			else
				setPermission(app, perm, ConsentType.DENIED);
		}

		case SIGNATURE:
		{
			if (app.appPackage.signature == perm.definer.appPackage.signature)
				setPermission(app, perm, ConsentType.ALLOWED);
			else
				setPermission(app, perm, ConsentType.DENIED);
		}

		case RUNTIME:
		case SPECIAL:
		{
			askUser(app, perm);
		}

		case URI:
		case CUSTOM:
		{
			checkUriOrCustomPermission(app, perm);
			break;
		}
		}

		return getPermission(app, perm);
	}

	public static PermissionManager getInstance()
	{
		if (instance == null)
			instance = new PermissionManager();

		return instance;
	}

	private void askUser(Application app, Permission perm)
	{
		randomPermissionResult(app, perm);
	}

	private void checkUriOrCustomPermission(Application app, Permission perm)
	{
		randomPermissionResult(app, perm);
	}

	private void randomPermissionResult(Application app, Permission perm)
	{
		Random rand = new Random();

		int userDecision = rand.nextInt(4);

		if (userDecision == 0)
		{
			setPermission(app, perm, ConsentType.ALLOWED);
		}
		else if (userDecision == 1)
		{
			setPermission(app, perm, ConsentType.DENIED);
		}
		else if (userDecision == 2)
		{
			setPermission(app, perm, ConsentType.ONLY_ONCE);
		}
		else if (userDecision == 3)
		{
			setPermission(app, perm, ConsentType.WHILE_USING_APP);
		}
	}

	private Map<Permission, ConsentType> getAppPermissions(Application app)
	{
		if (!appPerms.containsKey(app))
			appPerms.put(app, new HashMap<Permission, ConsentType>());

		return appPerms.get(app);
	}

	private ConsentType getPermission(Application app, Permission perm)
	{
		Map<Permission, ConsentType> map = getAppPermissions(app);

		if (!map.containsKey(perm))
			map.put(perm, null);

		return map.get(perm);
	}

	private void setPermission(Application app, Permission perm,
			ConsentType consent)
	{
		Map<Permission, ConsentType> map = getAppPermissions(app);
		map.put(perm, consent);
	}
}

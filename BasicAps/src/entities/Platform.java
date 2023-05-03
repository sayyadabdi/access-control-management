package entities;

import java.util.List;

public class Platform
{

	public List<Datum> data;

	public List<Action> actions;

	public List<Permission> permissions;
	
	public List<PermissionGroup> permissionGroups;

	public List<Application> applications;

	public List<PermissionHistory> permissionUseHistories;

	public Platform()
	{

	}

	public void install(Application a)
	{
	}

	public void uninstall(Application a)
	{
	}

	public void update(Application a)
	{
	}
}

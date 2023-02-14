package core;

import permission.Permission;

public interface IPermissionRequest
{
	public PermissionRequestDecision ask(process.Process proc, Permission perm);
}

package entities;

import java.util.List;

public class PermissionGroup
{
	// If one permission is granted, then all others are granted too.
	public List<Permission> permissions;
}

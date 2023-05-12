package entities;

import enums.PermissionType;
import enums.ProtectionLevel;

public class Permission
{

	public String name;

	public PermissionType type;

	public Application definer;

	public ProtectionLevel protectionLevel;
}

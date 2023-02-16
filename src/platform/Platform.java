package platform;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Random;

import ac.AccessControlManager;
import permission.Permission;
import resource.Resource;

public class Platform
{
	private List<Resource> resources;

	private List<process.Process> processes;

	private List<Permission> permissions;

	private HashMap<Permission, List<Resource>> permMap;

	public Platform()
	{
		resources = new ArrayList<>();
		processes = new ArrayList<>();
		permissions = new ArrayList<>();
		permMap = new HashMap<>();

		for (int i = 1; i <= 5; i++)
		{
			this.resources.add(new Resource());
		}

		for (int i = 1; i <= 5; i++)
		{
			this.permissions.add(new Permission());
		}

		for (int i = 1; i <= 2; i++)
		{
			this.processes.add(new process.Process());
		}
	}

	public void start()
	{
		var random = new Random();
		for (Permission p : this.permissions)
		{
			List<Resource> list = new ArrayList<>();
			this.permMap.put(p, list);

			for (Resource r : this.resources)
			{
				if (random.nextBoolean())
					list.add(r);
			}
		}

		new AccessControlManager();
	}
}

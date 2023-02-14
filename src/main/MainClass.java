package main;

import platform.Platform;

public class MainClass
{
	public static void main(String[] args)
	{
		System.out.println("Initializing the platform.");
		new Platform().start();
	}
}

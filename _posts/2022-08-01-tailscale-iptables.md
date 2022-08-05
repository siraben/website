---
layout: post
title: "Using Tailscale and iptables to roll your own port forwarding"
subtitle: "Or, how to host a Minecraft server without getting more hardware"
tags:
- network
- tailscale
- nixos
hasmath: true
---

## The problem
I want to play Minecraft with my friends, and I already have a server
exposed to the internet.  However, my server is severely underpowered
and is unable to run a Minecraft server instance.  On the other hand,
I have a spare beefy laptop that can easily handle the load, but
port-forwarding is not possible.  Both the server and the laptop are
on my [Tailscale](https://tailscale.com) network.  Could I somehow
leverage all of this to spin up a Minecraft server with a public IP?
The answer was yes---and I was surprised at how easy it all was.  As a
plus, the server is very playable and the latency was better than
trying out random "free hosting" services.

<center>
<p><img src="/assets/tailscale-iptable.svg" alt="Graphic"></p>
</center>

## Halfway with Tailscale
I already use Tailscale on all my devices, so of course when I spin up
a Minecraft server instance on one device I can immediately connect to
it from my other ones.  However my friends do not have Tailscale
(yet!), so unfortunately [node
sharing](https://tailscale.com/kb/1084/sharing/) is out of the picture
for now.  However I can still take advantage of Tailscale in that my
laptop will always have a static IP relative to the server, and the
server will always have a static IP relative to the public internet.
So altogether the connection will be deterministic and I don't have to
resort to any dynamic shenanigans.


Let's test the theory.

```ShellSession
$ NIXPKGS_ALLOW_UNFREE=1 nix run --impure nixpkgs#minecraft-server
Starting net.minecraft.server.Main
[22:18:53] [ServerMain/INFO]: Building unoptimized datafixer
[22:18:54] [ServerMain/INFO]: Environment: authHost='https://authserver.mojang.com', accountsHost='https://api.mojang.com', sessionHost='https://sessionserver.mojang.com', servicesHost='https://api.minecraftservices.com', name='PROD'
[22:18:54] [ServerMain/INFO]: Loaded 7 recipes
[22:18:55] [ServerMain/INFO]: Loaded 1179 advancements
[22:18:55] [Server thread/INFO]: Starting minecraft server version 1.19.1
[22:18:55] [Server thread/INFO]: Loading properties
[22:18:55] [Server thread/INFO]: Default game type: SURVIVAL
[22:18:55] [Server thread/INFO]: Generating keypair
[22:18:55] [Server thread/INFO]: Starting Minecraft server on *:25565
[22:18:55] [Server thread/INFO]: Using default channel type
[22:18:55] [Server thread/INFO]: Preparing level "world"
[22:18:55] [Server thread/INFO]: Preparing start region for dimension minecraft:overworld
[22:18:56] [Worker-Main-1/INFO]: Preparing spawn area: 0%
[22:18:56] [Worker-Main-1/INFO]: Preparing spawn area: 0%
[22:18:56] [Worker-Main-7/INFO]: Preparing spawn area: 0%
[22:18:57] [Worker-Main-7/INFO]: Preparing spawn area: 0%
[22:18:57] [Worker-Main-1/INFO]: Preparing spawn area: 83%
[22:18:57] [Server thread/INFO]: Time elapsed: 2080 ms
[22:18:57] [Server thread/INFO]: Done (2.163s)! For help, type "help"
```

And let's check if Minecraft can see it...

<center><p><img src="/assets/server-entry.png"></p></center>

Great success!  Now we just need to expose it to the public internet.

## iptables to the rescue!
`iptables` essentially lets you configure the rules of the Linux
kernel firewall.  Conceptually it's quite simple.  The user defines
_tables_ and when a packet comes in, it goes through _chains_ of
_rules_ in the tables and you can route the packet through essentially
whatever treatment you like.  Java edition Minecraft servers use TCP
port 25565 between the client and server.

### NixOS configuration
It was very straightforward to enable IP forwarding and add 25565 to
the list of open TCP ports for my server:

```nix
# combine with the rest of your configuration
{
   boot.kernel.sysctl."net.ipv4.ip_forward" = 1;
   networking.firewall.allowedTCPPorts = [ 25565 ];
}
```

### Creating the rule
Now we can go ahead add the following commands to our firewall setup.
Let `dest_ip` be the Tailscale IP of the server.  The first command
adds a rule to the `PREROUTING` chain which is where packets arrive
before being processed.  We basically immediately forward the packet
over to the laptop pointed to by the IP address given by Tailscale.
The second command essentially lets the source IP of the packet remain
the same so the server just acts as a router.

```nix
# combine with the rest of your configuration
{
  networking.firewall.extraCommands = ''
   IPTABLES=${pkgs.iptables}/bin/iptables
   "$IPTABLES" -t nat -A PREROUTING -p tcp --dport 25565 -j DNAT --to-destination ${dest_ip}:25565
   "$IPTABLES" -t nat -A POSTROUTING -j MASQUERADE
  '';
}
```

Now we have the following setup:

<center>
<p><img src="/assets/tailscale-iptable.svg" alt="Graphic"></p>
</center>

And checking again in Minecraft, this time using the public server IP,
it all works as expected!

### Final touches: a DNS record
For the final touches *\*chef's kiss\**, adding an A record gave me
a nice URL I could give people instead of an IP address.

## Performance
As far as performance goes, it's pretty good!  The proxy server is on the
East coast and even though the Minecraft server is on the West coast,
having played on it for several hours today, my friends and I had no
problems whatsoever.  I pinged people through the connection and
latency was acceptable (77 ms for someone in New York).

## References
[Xe's Tailscale on NixOS post](https://tailscale.com/blog/nixos-minecraft/)
inspired me to write this, however my requirements were different.  I
did not want to require my friends to install Tailscale to play on my
server, and wanted to leverage the existing hardware I had access to,
essentially letting me use my server as a crappy router.

Various `iptables` tutorials and resources online helped me make sense
of the terminology, commands and flags.

---
layout: post
title: Dirty Nix flake quality-of-life hacks
tags:
- nix
date: 2022-02-12 22:09 -0600
---

[Nix flakes](https://www.tweag.io/blog/2020-05-25-flakes/) landed in
Nix (as an experimental option) with the [2.4
update](https://discourse.nixos.org/t/nix-2-4-released/15822) a few
months ago, and represents a substantial change in how projects using
Nix can standardize their outputs, inputs and ensure reproducibility.

Nevertheless, this hermeticity comes with some downsides, especially
when it comes to bandwidth, disk space and CPU usage.  The reason for
this is that [Nixpkgs](https://github.com/NixOS/nixpkgs/) occasionally
merges PRs that "rebuild the world," for instance, [staging next
cycles](https://github.com/NixOS/nixpkgs/pull/138268), or urgent
updates to OpenSSL and other critical packages (which cause a rebuild
in say, Vim because it affects the git derivation used to fetch it.)
Thus when you want to use a package that depends on an older or newer
commit of Nixpkgs and some mass-rebuild PR landed in the intervening
time, you'll be faced with mass downloads of almost every dependency
that probably did not change in terms of build contents, but whose
build environments differed enough that Nix considers them
different.

After over a year of using flakes in practice, I've noticed certain
ways in which I overcome these inconveniences, which I'll elaborate
below.

Note that this isn't to say the hacks are without drawbacks.  I'll
make it apparent in each hack what the benefits and drawbacks are.

## Avoiding mass rebuilds with input overriding
**Scenario:** want to avoid a mass rebuild when trying to build an
older project

**Fix:** override the `nixpkgs` input with a fixed reference

**Drawbacks:** might lose reproducibility, but it's fine if the
changes weren't major between the pinned commit and overriden one

Around a year ago, I started [pinning my Nixpkgs
registry](https://github.com/siraben/dotfiles/commit/217c02265596df27ae392840f656eff5d5446169).
This lets me keep my flake reference to `nixpkgs` consistent across my
systems (as opposed to using channels.)  This is good when running
commands with `nix run` so that instead of using the most up-to-date
commit of Nixpkgs, it uses the pinned one from my system instead.

I then deploy my server configuration using a [simple
tool](https://github.com/winterqt/deploy).  So when I want to update
my server I run the following command

```
$ nix run github:winterqt/deploy -- siraben-land
[0/81 built, 1/0/14 copied (3.7/924.4 MiB), 1.0/161.4 MiB DL] fetching llvm-13.0.0-lib from https://cache.nixos.org
```

Huh?  What does LLVM have to do with using the deployment tool?  Why
are there 81 rebuilds?  Such scenarios are commonplace in my
experience, due to the gap between what the package set Nixpkgs to and
where Nixpkgs is currently.  The solution is thus to override the
flake input altogether.  Many flake commands accept the
`--override-input` flag that takes two arguments; a path to override
and the new flake reference to override it with.  In the following
command I'm overriding the input called `nixpkgs` with `nixpkgs` from
my registry.

```ShellSession
$ nix run github:winterqt/deploy --override-input nixpkgs nixpkgs --siraben-land
warning: not writing modified lock file of flake 'github:winterqt/deploy':
• Updated input 'nixpkgs':
    'github:NixOS/nixpkgs/5c37ad87222cfc1ec36d6cd1364514a9efc2f7f2' (2021-12-25)
  → 'github:NixOS/nixpkgs/a529f0c125a78343b145a8eb2b915b0295e4f459' (2022-01-31)
```

Notice that the reference to Nixpkgs went *back* in time by a month.
In this case, I avoided rebuilds and the server config deployed
without any problems.  Of course, the natural downside to this is that
you might lose reproducibility if there were major changes between the
two commits.  In most non-critical cases, the resources and time saved
are worth the risk.

## Importing a path when using a Nix command
**Scenario:** when working with a pre-flakes project, we want to be
able to build a derivation specified with a given expression

**Fix:** pass the `--impure` flag

**Drawbacks:** could lead to larger closure sizes

In the world of Nix flakes, impure references to things as such as the
current directory are outright banned.  For instance, suppose we're on
`aarch64-darwin` and we want to build GNU Hello for `x86_64-darwin`,
before flakes we might run

```ShellSession
$ nix-build -E 'with (import ./. {system="x86_64-darwin";}); hello'
```

So the Nix command equivalent would be

```ShellSession
$ nix build --expr 'with (import ./. {system="x86_64-darwin";}); hello'
error: access to absolute path '/Users/siraben/Git/forks/nixpkgs' is forbidden in pure eval mode (use '--impure' to override)
(use '--show-trace' to show detailed location information)
```

As the error message suggests, we have to pass `--impure` to it,
resulting in

```ShellSession
$ nix build --impure --expr 'with (import ./. {system="x86_64-darwin";}); hello'
```

which succeeds as usual.  Note that this might lead to increased
closure sizes because a path reference results in the entire directory
of the package being copied to the Nix store.

## Building unfree or unsupported packages
**Scenario:** want to build unfree packages or packages that are
marked as broken for the current platform

**Fix:** pass `--impure` to `nix build`

**Drawbacks:** mostly harmless™

As an example, the [math-comp](https://github.com/math-comp/mcb) book has a
`flake.nix` file defined.  So we might be tempted to try to build the
book with flakes:

```ShellSession
$ nix build github:math-comp/mcb
error: Package ‘math-comp-book’ in /nix/store/z5d23mcmv3va30nfkg1q40iz62xyi57a-source/flake.nix:36 has an unfree license (‘cc-by-nc-40’), refusing to evaluate.

       a) To temporarily allow unfree packages, you can use an environment variable
          for a single invocation of the nix tools.

            $ export NIXPKGS_ALLOW_UNFREE=1

       b) For `nixos-rebuild` you can set
         { nixpkgs.config.allowUnfree = true; }
       in configuration.nix to override this.

       Alternatively you can configure a predicate to allow specific packages:
         { nixpkgs.config.allowUnfreePredicate = pkg: builtins.elem (lib.getName pkg) [
             "math-comp-book"
           ];
         }

       c) For `nix-env`, `nix-build`, `nix-shell` or any other Nix command you can add
         { allowUnfree = true; }
       to ~/.config/nixpkgs/config.nix.
(use '--show-trace' to show detailed location information)
```

Unfortunately in this case it's not clear what the fix is.  Even if
you set that environment variable, you still get the same error
message.  Again harkening back to the philosophy of Nix flakes,
querying environment variables is considered impure.  The fix is to
again pass the `--impure` flag while setting the environment variable
at the same time.


```
$ NIXPKGS_ALLOW_UNFREE=1 nix build --impure github:math-comp/mcb && tree ./result
./result
└── share
    └── book.pdf
```

There really isn't any downside to this method, as far as I know.
Unless environment variables you set in your shell also affect other
aspects of the build, everything should be the same, and you'll be
able to run and build packages that were marked as broken or unfree
previously.

## Final thoughts
Nix flakes isn't to blame for these workarounds arising per se.  In a
sense, Nix becomes *too* pure to the extent where resources are being
used when they don't strictly need to, especially for non-critical use
cases.  In the future, features such as a [content-addressed
store](https://www.tweag.io/blog/2020-09-10-nix-cas/) may help with
issues such as mass rebuilds, where package hashes are determined by
their build contents and not their input derivations.

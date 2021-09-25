---
layout: post
title: "Organizing theories in Coq: a comparison"
tags:
- coq
- programming
---

Design patterns? In Coq?  The hard truth about software engineering is
that non-trivial developments in any programming language need some
uniform structure on them, so that they can be reasoned about and
combined compositionally.  Imagine OCaml without its module system, or
Java without interfaces, or C without header files.  What these
features all share is that they let us separate the abstract interface
of a datatype from its implementation details.  In the same spirit, in
developments of theories in proof assistants, it is necessary to also
have such abstractions, both as a matter of programming and as a
matter of keeping in line with mathematical practice.  For instance,
in a proof we might start off with "Let F be a field...," and from
that we immediately inherit all of the theories of fields, rings and
groups that we can use later on in the proof.

> The key to understanding complex systems is knowing what _not_ to
> think. - Gerald Sussman

There's a lot of literature on "proving in the small" in Coq.  For
instance, [Software
Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/toc.html)
is a whole series dedicated to various aspects of computer science and
programming language semantics formalized in Coq.  However, when it
comes to a [Coq for the working
mathematician](https://mathoverflow.net/questions/155909/wanted-a-coq-for-the-working-mathematician),
there's still a gap to be filled. In this article I will catalogue and
explain various patterns I've encountered and their strengths and
benefits.  Such patterns include:

- typeclasses
- hierarchy builder
- modules
- records
- structures and telescopes
- packed classes and canonical structures

For convenience I will start with the most recommended elegant and
boilerplate-free patterns to the ugliest ones.

The running example will be a simple algebraic hierarchy: semigroup,
monoid, commutative monoid, group, Abelian group.  That should be
elaborate enough to show how the approaches hold up in a more
realistic setting.  Here's an overview of the hierarchy we'll be
building over a type `A`:

- Semigroup
  - `add : A -> A -> A`
  - `addrA : associative add`
- Monoid (inherits from Semigroup)
  - `idm : A`
  - `add0r : left_id idm add`
- Com_Monoid (inherits from Monoid)
  - `addrC : commutative add`
- Group (inherits from Monoid)
  - `opp : A -> A`
  - `addNr : forall x, add (opp x) x = idm`
- Com_Group (inherits from Com_Monoid and Group)
g
<br><center><img src="/assets/alg.svg"></center><br>

Then, if all goes well, we will test the expressiveness of the pattern
by proving a simple theorem, which makes use of every law from
every structure.

```coq
(* For A an instance of Com_Group *)
Lemma example A (a b : A) : add (add (opp b) (add b a)) (opp a) = idm.
Proof. by rewrite addrC (addrA (opp b)) addNr add0r addNr. Qed.
```
## Typeclasses
An alternative way to structure the hierarchy is to use typeclasses.
This goes very well, our declaration for `Com_Group` is just the
constraints.  However, pay special attention to the definition of
`Com_Group`, there's a `!` in front of the `Com_Monoid` constraint to
expose the implicit arguments again, so that it can implicitly inherit
the monoid instance from `G`.

```coq
Require Import ssrfun ssreflect.

Class Semigroup (A : Type) (add : A -> A -> A) := { addrA : associative add }.

Class Monoid A `{M : Semigroup A} (idm : A) := { add0r : left_id idm add }.

Class Com_Monoid A `{M : Monoid A} := { addrC : commutative add }.

Class Group A `{M : Monoid A} (opp : A -> A) := {
  addNr : forall x, add (opp x) x = idm
}.

Class Com_Group A `{G : Group A} `{CM : !Com_Monoid A}.
```

The example lemma is easily proved, showing the power of typeclass
resolution in unifying all the structures.

```coq
Lemma example A `{M : Com_Group A} :
  forall (a b : A), add (add (opp b) (add b a)) (opp a) = idm.
Proof. move=> a b. by rewrite addrC (addrA (opp b)) addNr add0r addNr. Qed.
```

See the accompanying gist for the instantation of the structures over
ℤ.

## Hierarchy Builder
The
[hierarchy-builder](https://github.com/math-comp/hierarchy-builder)
(HB) package is best described as a boilerplate generator, but in a
good way!  From a usability point of view, it is similar to
typeclasses, though one has to be a bit more explicit about the
transitive instances (see below).

How is works is that the underlying code it generates follows a
pattern known as _packed classes_ (elaborated in the next section),
and for future-proofing the generated code can be shown by prefixing a
HB command with `#[log]`:

## Packed classes
In the [math-comp](https://math-comp.github.io/) library, the approach
taken is known as the _packed classes_ design pattern.  I would
probably do a more elaborate
## Modules
One approach, seen in [CPDT](http://adam.chlipala.net/cpdt/) is to use
the module system to organize the hierarchy.  It seems fine for the
first few structures.  We declare parameterized modules and postulate
additional axioms upon the structure from which it is inheriting from.

```coq
Require Import ssrfun.

Module Type SEMIGROUP.
  Parameter A: Type.
  Parameter Inline add: A -> A -> A.
  Axiom addrA : associative add.
End SEMIGROUP.

Module Type MONOID.
  Include SEMIGROUP.
  Parameter idm : A.
  Axiom add0r : left_id idm add.
End MONOID.

Module Type COM_MONOID.
  Include MONOID.
  Axiom addrC : commutative add.
End COM_MONOID.

Module Type GROUP.
  Include MONOID.
  Parameter opp : A -> A.
  Axiom addNr : forall x, add (opp x) x = idm.
End GROUP.
```

However, we immediately run into an issue when trying to create a
Abelian group from a commutative monoid and group, this is because the
carrier type `A` is already in scope from the first include, so we
cannot share the carrier type (or even the underlying monoid) with
`GROUP`.  So we give up.


```coq
Module Type COM_GROUP.
  Include COM_MONOID.
  Fail Include GROUP.
End COM_GROUP.
```

```
The command has indeed failed with message:
The label A is already declared.
```

## Structures
Let's define a semigroup using one of the most basic features of Coq,
structures (AKA records).

```coq
Require Import ssrfun.

Structure Semigroup : Type := makeSemigroup {
  A :> Set;
  add : A -> A -> A;
  addrA : associative add;
}.
```

## Telescopes
The _telescopes_ pattern is relatively easy to get started with, and
is similar to record-based patterns used across the Coq ecosystem.

Here's how to define a monoid.  We create a module, postulate a type
`T` and an identity element `idm` of type `T`, and combine the laws
into a record called `law`.  The exports section is small here but we
export just the `operator` coercion.

```coq
Module Monoid.

Section Definitions.
Variables (T : Type) (idm : T).

Structure law := Law {
  operator : T -> T -> T;
  _ : associative operator;
  _ : left_id idm operator;
  _ : right_id idm operator
}.

Local Coercion operator : law >-> Funclass.

End Definitions.

Module Import Exports.

Coercion operator : law >-> Funclass.

End Exports.
End Monoid.

Export Monoid.Exports.
```

With that defined, we can instantiate the monoid structure for
booleans (note that `idm` is automatically unified with `true`).

```coq
Import Monoid.

Lemma andbA : associative andb. Proof. by case. Qed.
Lemma andTb : left_id true andb. Proof. by case. Qed.
Lemma andbT : right_id true andb. Proof. by case. Qed.

Canonical andb_monoid := Law andbA andTb andbT.
```


Programming and mathematics have much in common, philosophically.

The disciplines deal with constructions of various kinds,

As a result, it's no surprise that concepts such as overloaded
notations, implicit coercions and inheritance pop up frequently in
both disciplines.  For instance, a field inherits the properties of a
ring, which in turn inherit from Abelian groups.  Mathematical
structures even exhibit multiple inheritance.  An
[algebra](https://en.wikipedia.org/wiki/Algebra_over_a_field) is a
ring and also a module.  Mathematics is abound with rich structures.
For instance, here's the dependency graph of the real number type in
the [mathcomp-analysis](https://github.com/math-comp/analysis/)
library.

![Dependency graph of real numbers in
mathcomp-analysis](/assets/real-hierarchy.png)

From left to right, the structures can be roughly classified as
pertaining to order theory, algebra and topology.

The higher up one goes in mathematics, the
more nuanced and

Thus, when organizing mathematical theories in a proof assistant, we
can learn from best practices in both disciplines.

A numeric type is a recurring theme in programming languages.
Clearly, it would be a bad idea to have specialized notation just to
add `int`

An algebraic structure is a recurring theme in mathematics.  We start
from a set with a binary operation, postulate some laws about how that
operation should behave, perhaps adding constants and other operations
along the way.  In this way

> The first and most important one is that formal proofs are just computer code about mathematical proofs, hence good practices in both domains are likely to apply to formal proofs too.

<!-- some random commentary about programming and math -->

Imagine you had to start programming from scratch again.  At first,
the programs you write are nice and small, they can be held in your
head fully and teased apart.  These are the types of programs you see
they are [elegant weapons](https://xkcd.com/297/).

Let's pretend we're creating a book that will contain all mathematical
knowledge starting from nothing but formal logic. At first, there are
few constructions.  Maybe you define the natural numbers and start
fleshing out number theory, then you realize some abstract algebra
would be useful, and define rings and fields ...


It's hard to really appreciate just how much structure there is behind
a mathematical concept.  Take, for instance, the real numbers and
suppose that you want to explain it to a person from scratch.
Fortunately, this already has been done, albeit to a computer instead.
Here's the inheritance hierarchy of the real number type in the
[mathcomp-analysis](https://github.com/math-comp/analysis/) library.

![Dependency graph of real numbers in
mathcomp-analysis](/assets/real-hierarchy.png)

We can break it down roughly into three parts.  On the left there's
order theory; posets and lattices (with many subtle flavors of them).
In the middle there's algebra; rings, domains and fields (again with
different flavors), and on the right there's topology; topological
spaces, metric and pseudometric spaces.  Even with this distinction,
we can see multiple inheritance everywhere!  For instance, you could
conjure up a partially-ordered domain equipped with a norm.  How do
you make expressing this ergonomic?



## Equality as an interface




From a software eng

[Programming in the large](https://en.wikipedia.org/wiki/Programming_in_the_large_and_programming_in_the_small) is hard.

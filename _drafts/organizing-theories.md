---
layout: post
title: "Organizing theories in Coq: a comparison"
tags:
- coq
- programming
---

Programming and mathematics have much in common, philosophically.  The
disciplines deal with constructions of various kinds.  The
constructions can get arbitrarily complex and interconnected.  As a
result, it's no surprise that concepts such as overloaded notations,
implicit coercions and inheritance pop up frequently in both
disciplines.  For instance, a field inherits the properties of a ring,
which in turn inherit from Abelian groups.  Mathematical structures
even exhibit multiple inheritance, and such examples are plentiful.
For instance, here's the dependency graph of the real number type in
the [mathcomp-analysis](https://github.com/math-comp/analysis/)
library.

![Dependency graph of real numbers in
mathcomp-analysis](/assets/real-hierarchy.png)

From left to right, the structures can be roughly classified as
pertaining to order theory, algebra and topology.  For the
object-oriented programmer: how many instances of multiple inheritance
do you see?

It's important to capture the way structures are organized in
mathematics in a proof assistant with some uniform strategy,
well-known in the OOP world as "design patterns."  In this article I
will catalogue and explain a selection of various patterns and their
strengths and benefits.  They are:

- typeclasses
- hierarchy builder
- modules
- records
- structures and telescopes
- packed classes and canonical structures

For convenience as a reference I will start with the most recommended
elegant and boilerplate-free patterns to the ugliest and broken ones.

The running example will be a simple algebraic hierarchy: semigroup,
monoid, commutative monoid, group, Abelian group.  That should be
elaborate enough to show how the approaches hold up in a more
realistic setting.  Here's an overview of the hierarchy we'll be
building over a type `A`:

<br><center><img src="/assets/alg.svg"></center><br>

- Semigroup
  - `add : A -> A -> A` (a binary operation over `A`)
  - `addrA : associative add` (`add` is associative)
- Monoid (inherits from Semigroup)
  - `idm : A`
  - `add0r : left_id idm add` (`idm` is a left identity for `add`)
  - `addr0 : right_id idm add` (`idm` is a right identity for `add`)
- Com_Monoid (inherits from Monoid)
  - `addrC : commutative add` (`add` is commutative)
- Group (inherits from Monoid)
  - `opp : A -> A` (`inverse` function over `A`)
  - `addNr : forall x, add (opp x) x = idm` (addition of an element
    with its inverse results in identity)
- Com_Group (inherits from Com_Monoid and Group)

Then, if all goes well, we will test the expressiveness of our
hierarchy by proving a simple lemma, which makes use of a law
from every structure.

```coq
(* Let A an instance of Com_Group, then the lemma holds *)
Lemma example A (a b : A) : add (add (opp b) (add b a)) (opp a) = idm.
Proof. by rewrite addrC (addrA (opp b)) addNr add0r addNr. Qed.
```
## Typeclasses
A well-known and vanilla approach is to use typeclasses.  This goes
very well, our declaration for `Com_Group` is just the constraints.
However, pay special attention to the definition of `Com_Group`,
there's a `!` in front of the `Com_Monoid` constraint to expose the
implicit arguments again, so that it can implicitly inherit the monoid
instance from `G`.

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

## Equality as an interface

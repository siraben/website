---
layout: post
title: 'A non-trivial trivial theorem: doing classical mathematics in Coq'
date: 2021-06-27 16:16 +0700
tags:
- coq
- math
---
After having gone through most of the first 3 books in [Software
Foundations](https://softwarefoundations.cis.upenn.edu/), and proving
various theorems in classical real analysis in Coq, I decided to
formalize some basic stuff from [Algebra: Chapter
0](https://bookstore.ams.org/gsm-104/), in particular the following
statement.

> Proposition 2.1. Assume A is non-empty, let `f : A -> B` be a
> function.  `f` has a left-inverse if and only if it is injective.

This is a pretty trivial statement with a pretty trivial proof on
paper (try it!), so I expected the Coq proof to be quite easy as well.
What I didn't know was that it would take me through a short journey
through mathematical foundations, computability and some philosophy of
mathematics as well.  Why was it harder than expected, and what does
it say about mathematics as a field?  I will replicate the dead-ends I
ran into here, to illustrate various points.

## A reasonable start

On the first attempt, I translated the statements as directly as
possible into Coq.  The forward direction is easy.

```coq
Definition injective {A B} (f : A -> B) :=
  forall a' a'', a' <> a'' -> f a' <> f a''.

Definition left_inverse {A B} (f : A -> B) g := forall a, g (f a) = a.

Definition right_inverse {A B} (f : A -> B) g := forall b, f (g b) = b.

Lemma P_2_1 {A B} (f : A -> B) (s : A) :
  (exists g, left_inverse f g) <-> injective f.
Proof.
  unfold left_inverse, injective.
  split; intros H.
  - intros a' a'' eq. destruct H as [g Hg].
    congruence.
  -
```

Now we prove the reverse direction, that if a function is injective,
then it has a left-inverse.  We have the following proof state:

```coq
  A : Type
  B : Type
  f : A -> B
  s : A
  H : forall a' a'' : A, a' <> a'' -> f a' <> f a''
  ============================
  exists g : B -> A, forall a : A, g (f a) = a
```

The goal is `exists g : B -> A, ...`.  In Coq we prove such statements
by providing the function `g` then showing indeed it is a
left-inverse.  The paper proof constructed such a `g` as well, so just
translate!

Here is the paper proof:

![Paper proof](/assets/backward-paper-proof.png "Proof of backwards implication from the book")

## Solving the halting problem
We have a function `g` that, given a `b`, returns an `a` if such an
`a` satisfying `b = f(a)` exists, or returns a fixed element `s` of
`f`.  Except, the devil is in the details, or in this case, in the
word _if_.  We have to make a decision depending on whether something
is in the image or not. Actually, if we can do this for arbitrary sets
`A` and `B`, we can solve the halting problem.  Here's a short proof:

Assume we can always tell if `b : B` is in the image of `f` or not.
Let `M` be a Turing machine.  Define `f : ℕ -> ℕ` where `f(n) = 0` if
`M` halts in `n` steps, otherwise return `n+1`.  This is obviously
injective.  So, what would `g(0)` give?  It would return the number of
steps that it takes for `M` to halt, or the fixed element `M`
diverges, but `M` is an arbitrary Turing machine, so that means we can
solve the halting problem.  (In fact you can also prove LEM from the
theorem, see Appendix B).

In type theory, all the functions we ever write are computable by
construction, so it actually turns out to be impossible to prove this
lemma as stated.  Thus, we need to strengthen our hypothesis, by
assuming that the condition is decidable.  In the Coq standard
library, there is the following datatype:

```coq
(** [sumor] is an option type equipped with the justification of why
    it may not be a regular value *)
Inductive sumor (A:Type) (B:Prop) : Type :=
  | inleft : A -> A + {B}
  | inright : B -> A + {B}
 where "A + { B }" := (sumor A B) : type_scope.
```

Essentially this an option type that gives the value of type `A` or a
proof why such a value cannot be produced.  This is important because
we want to use the left of the sum as the return value for the
left-inverse of `f`, and the right of the sum as a single bit to
decide to return the default value `s`.

```coq
(* Property of decidability of being in the image *)
Definition im_dec {A} {B} (f : A -> B) :=
  forall b, { a | f a = b } + ~ (exists a, f a = b).

(* If being in the image of an injective function f is decidable, it
   has a left inverse. *)
Lemma injective_left_inverse {A B} (s : A) (f : A -> B) :
  im_dec f -> injective f -> has_left_inverse f.
```

With this assumption, we can continue the proof, but then we
are stuck at following proof state.

```coq
  A : Type
  B : Type
  s : A
  f : A -> B
  dec : forall b : B, {a : A | f a = b} + (~ (exists a : A, f a = b))
  inj : forall a' a'' : A, a' <> a'' -> f a' <> f a''
  a', a : A
  Ha : f a = f a'
  ============================
  a = a'
```

We need to prove `a = a'`, which follows from `f` being injective,
however note that the hypothesis `inj` states the contrapositive
claim.

In an undergrad discrete math class, one quickly learns about the
contrapositive law in classical logic, `(P -> Q) <-> (¬ Q -> ¬ P)`.
It turns out that in type theory (more generally, in intuitionistic
logic), the forward implication is provable but the backward
implication requires double negation elimination, which is equivalent
to LEM.  As a result, we can make prove a slightly more general
theorem if we use the following definition of `injective`. The proof
that our definition of injectivity implies the one used in the book is
trivial.

```coq
(* New definition of injective *)
Definition injective {A B} (f : A -> B) :=
  forall a' a'', f a' = f a'' -> a' = a''.
(* Book's definition *)
Definition injective' {A B} (f : A -> B) :=
  forall a' a'', a' <> a'' -> f a' <> f a''.

(* injective generalizes injective' *)
Theorem injective_injective' : forall {A B} (f : A -> B),
  injective f -> injective' f.
Proof. unfold injective, injective'. auto. Qed.
```

With all this done, we can finally prove the backwards direction.  One
last twist is that we'll use a sigma type and make the proof
transparent using `Defined.` so that we can extract the computational
content later.

```coq
Lemma injective_left_inverse {A B} (s : A) (f : A -> B) :
  im_dec f -> injective f -> { g | left_inverse f g }.
Proof.
  unfold injective, has_left_inverse, im_dec.
  intros dec inj.
  (* It's decidable to check if b is in the image or not *)
  exists (fun b => match dec b with inl (exist _ a _) => a | inr _ => s end).
  intros a'.
  destruct (dec (f a')) as [[a Ha] | contra].
  - apply inj; auto.
  - exfalso. apply contra. exists a'; auto.
Defined.
```

## Recap and final thoughts

So, what did we learn from this not-so-trivial proof of a trivial
theorem?

- when we used the truth-value of properties of values over arbitrary
  types (in this case, checking if an element of `B` is in the image
  of a function), we might want this property to be _decidable_
- sometimes we can restate things in a more general way that make it
  easier to prove in type theory, while still being classically
  equivalent

This experience left me feeling a bit philosophical.  Note some of
these points are subjective, and I speak from my perspective as an
undergraduate in pure math and CS.

We lost a bit of symmetry.  What used to be a simple `<->` is now two
separate lemmas, where the backward direction takes a proof that
finding a preimage is decidable.  Did that make matters worse?  I
don't think so.  I think the central question is, what do we _want_
from this theorem?  We can obtain left-inverses of any injective
function, presumably we would want compute with the left-inverse!

If we used the law of the excluded middle anywhere, we would lose
computability.  But by paying careful attention and performing minor
adjustments to the theorem, we have still preserved computability, and
in fact can use this to find left-inverses of injective functions (see
Appendix A).

What does this say about using constructive type theory as a
foundation for mathematics at large?  This is a difficult question
that far more qualified researchers such as Andrej Bauer can answer
better than I can (I highly recommend [his talk on constructive
mathematics](https://www.youtube.com/watch?v=zmhd8clDd_Y)).  My naïve
view is that once a foundation such as set theory is fixed, it is
inevitable that "implementation details" will be used to the fullest
extent.  You can "just" check if something is in the image of an
arbitrary function and voila, you have your well-defined function!
You can "just" construct the set of all Turing machines that halt. No
words said about if it's computable or not.

Another analogous situation I ran into was when trying to formalize
concepts from differential topology, but the problem was at my very
feet, I couldn't prove [a function restricted to the whole domain is
equal to the original
function](https://github.com/coq-community/topology/issues/29#issuecomment-847493572),
something taken for granted in the classical world.  Or how about
quotients?  They are ubiquitous in mathematics, one can perform
quotients of groups, rings, topological spaces and more.  See this
[passionate discussion regarding setoid
hell](https://github.com/coq/coq/issues/10871).

On the other hand, type theory feels like the right logical system to
work in for CS.  Most proofs in CS are constructive anyway, making
them very easy to translate into Coq.  You also get nicer properties:
all functions are computable, all functions are
[Scott-continuous](https://cs.stackexchange.com/a/81018), or even
topologically continuous.  You can also extract computational content
from proofs.  See Appendix A for how the left-inverse of the successor
function can be obtained, something you couldn't easily do in a
set-theoretic setting.

Do we have to give up LEM have all these things?  Not necessarily.  To
quote Bauer from his talk,

> Constructive mathematics keeps silent about the law of the excluded
> middle.  We do not accept it, we do not deny it, we just don't use
> it. Particular cases of law of excluded middle might be OK, but you
> have to establish them first.

While `P \/ ¬ P` is not provable for an arbitrary proposition `P`, if
you can show it for some particular `P` (or a family of such `P`s),
[you regain classical
reasoning](https://coq.inria.fr/library/Coq.Logic.Decidable.html).
For further excellent discussion on this topic, I recommend [this
Zulip
discussion](https://coq.zulipchat.com/#narrow/stream/237977-Coq-users/topic/LEM.20vs.20decidability/near/243306508)
regarding LEM and decidability.

## References

- [Algebra: Chapter 0](https://bookstore.ams.org/gsm-104/)
- [Discussion of the same theorem on reddit](https://old.reddit.com/r/logic/comments/fxjypn/what_is_not_constructive_in_this_proof/)

## Appendix A: Extracting the computational content of the proof
Using the proof-as-programs principle, we can in fact obtain
left-inverses of functions, provided that being in the image is
decidable and that the function is injective.

```coq
Definition eq_dec A := forall (a1 a2 : A), a1 = a2 \/ a1 <> a2.

Lemma nat_eq_dec : eq_dec nat.
Proof.
  unfold eq_dec.
  induction a1; destruct a2; auto.
  destruct (IHa1 a2); auto using f_equal.
Qed.

Definition succ (n : nat) := S n.

Definition pred' : nat -> nat.
Proof.
  refine (fun n => _ (injective_left_inverse 0 succ _ _)).
  - intros H. destruct H as [g Hg]. exact (g n).
  - unfold im_dec.
    induction b.
    + right. intros H. destruct H; discriminate.
    + left. refine (exist _ b _). reflexivity.
  - unfold injective. intros a' a'' H. inversion H; auto.
Defined.

Eval compute in (pred' 1000). (* => 999 *)
```

**Exercise (3 stars):** define `double n = n + n` and derive its
left-inverse in a similar manner.  You'll need to prove that being in
the image of `double` is decidable and that it's injective.

## Appendix B: Proving LEM

Here's something wild, we can prove LEM from the backward direction of
the original theorem! (Assuming proof irrelevance)

```coq
Require Import ProofIrrelevance.

Lemma inj_left_inverse_implies_lem :
  (forall {A B} (f : A -> B), A -> injective f -> exists g, left_inverse f g)
  -> (forall (P : Prop), P \/ ~ P).
Proof.
  unfold left_inverse. intros H P.
  set (f := fun a : P + True => match a with | inl _ => inl I | inr _ => inr I end).
  pose proof (H _ _ f (inr I)).
  assert (Hf : injective f).
  {
    unfold injective; intros.
    destruct a', a''; try discriminate.
    - f_equal. apply proof_irrelevance.
    - destruct t, t0. reflexivity.
  }
  specialize (H0 Hf).
  destruct H0 as [g Hg].
  destruct (g (inl I)) eqn:E; auto. right.
  intros a. destruct t.
  replace (inl I) with (f (inl a)) in E by auto.
  rewrite Hg in E. inversion E.
Qed.
```

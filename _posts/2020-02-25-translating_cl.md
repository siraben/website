---
layout: post
title: Translating Common Lisp to Haskell---a case study
date: 2020-02-25 18:46 -0600
tags: [haskell,common-lisp]
---
Lisp programs have their own particular style, often involving mutable
state, macros, meta-programming and more, which is to be expected of
such a flexible language.  Haskell, on the other hand, seems to be a
different world altogether, encapsulating effects with monads, a
static [type
system](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system),
and occasionally, use of Template Haskell.

So how difficult would it be to translate a Common Lisp program to
Haskell, in a way that makes the translated code seem idiomatic?  The
answer is through a careful choice of what Haskell features to use, in
this case, monad transformers, but also a lesser-known technique---the
[tagless final](http://okmij.org/ftp/tagless-final/course/lecture.pdf)
style.

Get the full code [here](https://github.com/siraben/hasktran).

## The Common Lisp program: an assembler for FRACTRAN
A couple of years ago, malisper wrote a [blog
post](https://malisper.me/building-fizzbuzz-fractran-bottom/) on
writing an assembler for the esoteric programming language
[FRACTRAN](https://en.wikipedia.org/wiki/Fractran) in Common Lisp.
It's quite a nice display of the power of Common Lisp, particularly
the macro system.  We're going to display a Common Lisp code block
followed by its translated Haskell variant, when possible.

```lisp
(defparameter *cur-inst-prime* nil)
(defparameter *next-inst-prime* nil)
(defparameter *lisptran-labels* nil)
(defparameter *lisptran-vars* nil)
(defparameter *next-new-prime* nil)
```

Unsurprisingly, this global state is encapsulated with the state
monad.  `ExceptT` appears too because we want to be able to throw an
error when a label is not found in the map.  We're also using the
`Math.NumberTheory.Primes` package to generate the infinite stream of
primes for us.

```haskell
import qualified Data.Map as M
import qualified Math.NumberTheory.Primes as P
data CompState =
  CompState
    { currInstPrime, nextInstPrime :: Integer
    , labels, vars :: M.Map String Integer
    , primes :: [P.Prime Integer]
    , gensymCount :: Integer
    }
  deriving (Show)
newtype Comp a =
  Comp { runComp :: ExceptT String (State CompState) a }
  deriving ( Functor, Applicative, Monad, 
           , MonadState CompState, MonadError String)
```

`new-prime` generates a fresh prime and places it in
`*next-new-prime*`.  In our case, we have an infinite list of primes,
so `newPrime` should just advance the list and return the old head.

```lisp
(defun new-prime ()
  "Returns a new prime we haven't used yet."
  (prog1 *next-new-prime*
    (setf *next-new-prime*
          (loop for i from (+ *next-new-prime* 1)
                if (prime i)
                  return i))))
```
```haskell
newPrime :: Comp Integer
newPrime = do
  l <- gets primes
  modify (\s -> s {primes = tail l})
  return (P.unPrime (head l))
```

`advance` is a sequence of assignments, so the translation is
straightforward.

```lisp
(defun advance ()
  (setf *cur-inst-prime* *next-inst-prime*
        *next-inst-prime* (new-prime)))
```
```haskell
advance :: Comp ()
advance = do
  c <- gets nextInstPrime
  p <- newPrime
  modify (\s -> s {currInstPrime = c, nextInstPrime = p})
```

`prime-for-label` looks up a label and returns its value if found, and
inserts it otherwise. `prime-for-var` is defined similarly.

```lisp
(defun prime-for-label (label)
  (or (gethash label *lisptran-labels*)
      (setf (gethash label *lisptran-labels*)
            (new-prime))))
```
```haskell
primeForLabel :: String -> Comp Integer
primeForLabel label = do
  labels <- gets labels
  case M.lookup label labels of
    Just p -> return p
    Nothing -> do
      p <- newPrime
      modify (\s -> s {labels = M.insert label p labels})
      return p
```

## An awkward step
Now we run into a little bit of an issue;

```lisp
(defmacro deftran (name args &body body)
  "Define a Lisptran macro."
  (setf (gethash ',name *lisptran-macros*)
        (lambda ,args ,@body)))
```

We don't have macros in Haskell!  This is where our translation starts
to diverge.  In such a case, it is useful to read the rest of the Lisp
code and see the larger structures at play, in this case, how the
`deftran` macro is used, for instance, in the definitions of `addi`,
`subi` and `>=i`.

```lisp
(deftran addi (x y)
  (prog1 (list (/ (* *next* (expt (prime-for-var x) y))
                  *cur*))
    (advance)))
(deftran subi (x y) ((addi x ,(- y))))
(deftran >=i (var val label)
  (prog1 (let ((restore (new-prime)))
           (list (/ restore
                    (expt (prime-for-var var) val)
                    *cur-inst-prime*)
                 (/ (* (prime-for-label label)
                       (expt (prime-for-var var) val))
                    restore)
                 (/ *next-inst-prime* *cur-inst-prime*)))
    (advance)))
```

It would seem that we are stuck.  We could generate lists of
`Rationals`, but the use of `advance` forces us to use the State
monad.  Furthermore, in `subi`, it calls `addi`!

One approach would be to express the instructions as a data type;

```haskell
type Var = String
type Label = String
data Instr = Addi Var Int
           | Subi Var Int
           | Jge Var Int Label
           ...
```

But we lose a critical feature of macros, that they can be used in
other macros, such as `subi` calling `addi`, and when we add a new
instruction, we have to go through the entire codebase to handle the
extra case, this is the infamous _expression problem_.  Fortunately,
much work has been carried out in attempting to resolve this, with one
promising approach being the _tagless final approach_.  That is, can
express we `addi`, `subi` and more using a typeclass, rather than a
data declaration?  The answer is a resounding yes.

## A macro is a tagless final encoding!
```haskell
class MonadState repr => FracComp repr where
  lit :: Integer -> repr [Rational]
  label :: String -> repr [Rational]
  addi :: String -> Integer -> repr [Rational]
  jge :: String -> Integer -> String -> repr [Rational]
  gensym :: repr String
  subi :: String -> Integer -> repr [Rational]
  subi x y = addi x (-y)
```

Now the definition of `subi` looks just like the Lisp one!  What's
going on in this typeclass is that `repr` is a higher-kinded type,
`repr :: * -> *`.  The `FracComp` typeclass has a constraint, `repr`
has to support being a State monad, because we will need a notion of
sequencing label generation to assemble programs correctly.

This extends naturally to `deftran` definitions that have side
effects, for instance, `gensym` in `goto`.

```lisp
(deftran goto (label) `((>=i ,(gensym) 0 ,label)))
```
```haskell
goto :: FracComp repr => String -> repr [Rational]
goto dest = do
  g <- gensym
  jge g 0 dest
```

That's neat, but now we only have a typeclass, we need to actually
instantiate it.  Indeed, `Comp` can be made an instance of `FracComp`.

```haskell
instance FracComp Comp where
  addi x 0 = primeForVar x $> []
  addi x y = do
    g <- (^ abs y) <$> primeForVar x
    f <-
      if y < 0
        then (%) <$> gets nextInstPrime <*> ((* g) <$> gets currInstPrime)
        else (%) <$> ((* g) <$> gets nextInstPrime) <*> gets currInstPrime
    advance
    return [f]
  gensym = newsym
newsym = do
  n <- gets gensymCount
  modify (\s -> s {gensymCount = n + 1})
  return ('t' : show n)
```

There's a little bit of a hiccup when `y` is negative, because raising
to a negative exponent raises an error.  Otherwise, the code is
remarkably close to Lisp.

Now we need to actually assemble a program.  `assemble` initializes
the state to the initial state.

```lisp
(defun assemble (insts)
  "Compile the given Lisptran program into Fractran. 
   Returns two values. The first is the Fractran program 
   and the second is the alphabet of the program."
  (let* ((*cur-prime* 2)
         (*cur-inst-prime* (new-prime))
         (*next-inst-prime* (new-prime))
         (*lisptran-labels* (make-hash-table))
         (*lisptran-vars* (make-hash-table)))
    (values (assemble-helper insts)
            (alphabet *lisptran-vars*))))
```
```haskell
initState =
  let (c:n:p) = P.primes
   in (CompState
         { currInstPrime = P.unPrime c
         , nextInstPrime = P.unPrime n
         , primes = p
         , labels = mempty
         , vars = mempty
         , gensymCount = 0
         })
run a = a & runComp & runExceptT & (`evalState` initState)
```

Now, we want to run the assembler. Something like this;

```
λ> [addi "x" 3] :: FracComp repr => [repr [Rational]]
λ> assemble [addi "x" 3] :: FracComp f => f [Rational]
```

So, `assemble` should have the following type:
```haskell
assemble :: FracComp repr => [repr [Rational]] -> repr [Rational]
```
We can calculate it as follows;

```
λ> :t [addi "x" 3]
it :: FracComp repr => [repr [Rational]]
λ> :t sequence [addi "x" 3]
it :: FracComp m => m [[Rational]]
λ> :t concat <$> sequence [addi "x" 3]
it :: FracComp f => f [Rational]
```

And for kicks, we can generalize `concat` to `join`, yielding our final
result.

```haskell
assemble :: (Traversable m, Monad m, Monad f) => m (f (m a)) -> f (m a)
assemble l = join <$> sequence l
```
```
λ> run (assemble [addi "x" 3])
Right [375 % 2]
```

The genius of the tagless final approach is that it lets us define new
data _variants_, in this case, new modular pieces of FRACTRAN code.

Some examples;
```lisp
(deftran while (test &rest body)
  (let ((gstart (gensym))
        (gend (gensym)))
    `((goto ,gend)
      ,gstart
      ,@body
      ,gend
      (,@test ,gstart))))

(deftran zero (var)
  `((while (>=i ,var 1)
      (subi ,var 1))))

(deftran move (to from)
  (let ((gtemp (gevnsym)))
    `((zero ,to)
      (while (>=i ,from 1)
        (addi ,gtemp 1)
        (subi ,from 1))
      (while (>=i ,gtemp 1)
        (addi ,to 1)
        (addi ,from 1)
        (subi ,gtemp 1)))))
```
```haskell
while test body = do
  gstart <- gensym
  gend <- gensym
  assemble
    (concat [[goto gend,
              label gstart],
              body,
              [label gend, test gstart]])

zero var = while (jge var 1) [subi var 1]

move to from = do
  gtemp <- gensym
  assemble
    [ zero to
    , while (jge from 1)
        [addi gtemp 1, subi from 1]
    , while (jge gtemp 1)
        [addi to 1, addi from 1, subi gtemp 1]
    ]

adds a b = do
  gtemp <- gensym
  assemble
    [ while (jge b 1) [addi gtemp 1, subi b 1]
    , while (jge gtemp 1) [addi a 1, addi b 1, subi gtemp 1]
    ]
```

With the tagless final embedding, we can write Haskell functions that
generate FRACTRAN programs as easily as we construct values.  For
instance, a function that takes an integer `n` and returns a FRACTRAN
program that computes the sum of the numbers from 1 to `n` inclusive.

```haskell
sumTo :: FracComp repr => Integer -> [repr [Rational]]
sumTo n = [ addi "c" 0
          , addi "n" n
          , while (jge "n" 0)
              [adds "c" "n", subi "n" 1]]
```

Now let's see the assembler in action!

```
λ> runAssembler (sumTo 10)

Right [847425747 % 2,13 % 3,19 % 13,11 % 3,11 % 29,31 % 11,41 % 31,
23 % 11,23 % 47,2279 % 23,59 % 301,59 % 41,67 % 413,329 % 67,61 % 59,
73 % 61,83 % 73,71 % 61,71 % 97,445 % 71,707 % 89,103 % 5353,
103 % 83,109 % 5459,5141 % 109,107 % 103,113 % 749,113 % 19,
131 % 113,29 % 131,127 % 113]
```
## Going beyond: a pretty printer
We're done.  Let's see what directions we can take our newly
translated FRACTRAN assembler.  Since we used the tagless final
approach, we can do cool things such as interpreting the values under
a different _semantic domain_.  In other words, a fully assembled and
final (pun intended) program `FracComp f => f [Rational]` has a
concrete type that depends on the appropriate choice of `f`, which in
turn depends on the call site! In particular, we can let `f` be the
newtype `S`, defined as

```haskell
newtype S a = S { unS :: StateT Int (Writer [Doc]) a }
            deriving (Functor, Applicative, Monad,
                      MonadWriter [Doc], MonadState Int)
```

And write the `FracComp` instance for `S`.

```haskell
instance FracComp S where
  lit i = tell [text (show i)] $> []
  label l = tell ["label" <+> text l] $> []
  addi l x = tell ["addi"  <+> text l <+> text (show x)] $> []
  jge l x dest = tell ["jge" <+> text l <+> text (show x) <+> text dest] $> []
  gensym = gets (('g' :) . show) <* modify (+ 1)

pretty :: Traversable t => t (S a) -> Doc
pretty x = x
         & fmap unS
         & sequence
         & (`evalStateT` 0)
         & execWriter
         & vcat
```

`pretty` works by unwrapping the `t (S a)` to a stateful writer, then
handling the state and writing.

```haskell
-- Traversable t
pretty x = x                :: t (S a)
         & fmap unS         :: t (StateT Int (Writer [Doc]) a)
         & sequence         :: StateT Int (Writer [Doc]) (t a)
         & (`evalStateT` 0) :: Writer [Doc] (t a)
         & execWriter       :: [Doc]
         & vcat             :: Doc
```

```
λ> pretty (sumTo 10)
addi n 10
jge g2 0 g1
label g0
jge g6 0 g5
label g4
addi g3 1
addi n -1
label g5
jge n 1 g4
jge g9 0 g8
label g7
addi c 1
addi n 1
addi g3 -1
label g8
jge g3 1 g7
addi n -1
label g1
jge n 0 g0
```

But we have just defined the pretty printers for the basic opcodes,
let's also write specialized printers for the high-level constructs
like `while`.  Once again, tagless final helps us achieve this.

```haskell
instance FracComp S where
  lit i = tell [text (show i)] $> []
  label l = tell ["label" <+> text l] $> []
  addi l x = tell [text l <+> "+=" <+> text (show x)] $> []
  jge l x dest = tell [text l <+> ">=" <+> (text (show x) <+> text dest)] $> []
  gensym = gets (('g' :) . show) <* modify (+ 1)
  --------------------------------------------------------------
  jle l x dest = tell [text l <+> "<=" <+> (text (show x) <+> text dest)] $> []
  adds l x = tell [text l <+> "+=" <+> text x] $> []
  subi l x = tell [text l <+> "-=" <+> text (show x)] $> []
  goto l = tell ["goto" <+> text l] $> []
  while test body = do
    censor ((\x -> "while " <> x <> "{") <$>) (test "")
    censor (nest 2 <$>) (sequence body)
    tell ["}"]
    return []
```
As a result, we can now output FRACTRAN programs in a language
resembling C.
```
λ> pretty (sumTo 10)
c += 0
n += 10
while n >= 0 {
  c += n
  n -= 1
}
```
## Conclusion
Porting code can be challenging, as there are multiple facets to
consider, for instance, what if the target language lacked a feature
of the source language?  Keeping it idiomatic across paradigms adds
additional challenges.  In this translation, some Lisp functions were
omitted entirely, either because they were not needed or did not fit
with the model (for instance, the `assemble-helper` function).
Nevertheless, code translation is a (in my opinion) good way to deepen
understanding and practice.


Get the full code [here](https://github.com/siraben/hasktran).

---
layout: post
title: How to write a tree-sitter grammar in an afternoon
tags:
- parsing
- tree-sitter
---

Every passing decade, it seems as if the task of implementing a new
programming language becomes easier.  Parser generators take the pain
out of parsing, and can give us informative error messages.
Expressive type systems in the host language let us pattern-match over
a recursive syntax tree with ease, letting us know if we've forgotten
a case.  Property-based testing and fuzzers let us test edge cases
faster and more completely than ever.  Compiling to intermediate
languages such as LLVM give us reasonable performance to even the
simplest languages.

Say you have just created a new language leveraging the latest and
greatest technologies in PL land, what should you turn your sights to
next, if you want people to actually adopt and use it?  I'd argue that
it should be writing a
[tree-sitter](https://tree-sitter.github.io/tree-sitter/) grammar.
Before I elaborate what tree-sitter is, here's what you'll be able to
achieve much more easily:

- syntax highlighting
- pretty-printing
- linting
- IDE-like features in your editor (autocomplete, structure
  navigation, jump to definition)

And the best part is that you can do it in an afternoon!  In this post
we'll write a grammar for
[IMP](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html),
a simple imperative language, and you can get the source code
[here](https://github.com/siraben/tree-sitter-imp).

This post was inspired by my research in improving the developer
experience in
[FORMULA](https://github.com/siraben/tree-sitter-formula) and
[Spin](https://github.com/siraben/tree-sitter-promela).

## Why tree-sitter?
Tree-sitter is a parser generator tool.  Unlike other parser
generators, it especially excels at *incremental parsing*, creating
useful parse trees even when the input has syntax errors.  And best of
all, it's extremely fast and dependency-free, letting you parse the
entirety of the file on every keystroke in milliseconds.  The
generated parser is written in C, and there are many
[bindings](https://tree-sitter.github.io/tree-sitter/#language-bindings)
to other programming languages, so you can programmatically walk the
tree as well.

## A tree-sitter grammar for IMP
[IMP](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html)
is a simple imperative language often used as an illustrative example
in PL theory.

### Setting up the project
### Writing the grammar
#### Expressions
First we follow the grammar for expressions given in the chapter.
Here it is for reference.

```
a := nat
    | a + a
    | a - a
    | a * a
    | (a)

b := true
    | false
    | a = a
    | a <= a
    | ~b
    | b && b
```

`a` corresponds to arithmetic expressions and `b` corresponds to
boolean expressions.

This corresponds to the 

### Defining precedence and associativity
Let's try to compile it!  Here's what tree-sitter outputs:


In parsing, resolving precedence and associativity is an important
part of making sure our parse trees correspond to what we intuitively
read things.  In this case, we want multiplication to bind more
tightly than addition, that is, we want `4+5*3` to be parsed as
`4+(5*3)` instead of `(4+5)*3`, and we want to use parenthesis to make
it clear when we want expressions grouped a certain way.  In
tree-sitter, associativity can be declared with `prec.right` and
`prec.left` respectively, which takes two arguments; the precendence
number (higher is stronger) and the rule to apply it to.  So we can
write:

<!-- code with fixed associativity -->

Now the grammar compiles without any issues.

#### Statements
Now that we've defined expressions (wasn't that easy?) we can breeze
through the cases for defining statements:

```
c := skip | x := a | c ; c | if b then c else c end | while b do c end
```

### Testing the grammar
Phew, so now we have a grammar that tree-sitter compiles.  How do we
actually run it?  The tree-sitter CLI has two subcommands to help out
with this, `tree-sitter parse` and `tree-sitter test`.  The `parse`
subcommand takes a path to a file and parses it with the current
grammar, printing the parse tree to stdout.  The `test` subcommand
runs a suite of tests defined in a very simple syntax:

<!-- example of test file  -->

When we run `tree-sitter test`, we get a check if a test passed and a
cross if it failed, complete with a diff showing the expected
vs. actual parse tree:

<!-- example of running tree-sitter test with incorrect parse -->


### Syntax highlighting!
Believe it or not, that was pretty much all there is to writing a
tree-sitter grammar!  We can immediately put it to use by using it to
perform syntax highlighting.  Traditional syntax highlighting methods
used in editors rely on regex and ad-hoc heuristics to colorize
tokens, whereas since tree-sitter has access to the entire parse tree
it can not only color identifiers, numbers and keywords, but also can
do so in a context-aware fashion---for instance, highlighting local
variables and user-defined types consistently.

The `tree-sitter highlight` command lets you generate [syntax
highlighting](https://tree-sitter.github.io/tree-sitter/syntax-highlighting)
of your source code and render it in your terminal or output to HTML.

Here's the result of highlighting the following IMP program:

<!-- IMP program highlighted -->

And for a more realistic example, here's two images showing highlights
of [Formula](https://github.com/VUISIS/formula-dotnet) code, can you
guess which one is produced by tree-sitter?

<!-- formula example -->

## Where to go from here?
Creating a tree-sitter grammar is only the beginning.  Now that you
have a fast, reliable way to generate syntax trees even in the
presence of syntax errors, you can use this as a base to build other
tools on.


### Editor integration
- screenshot of emacs querying
- highlighting in emacs
- debugging parsers

### Linters
Once you have a syntax tree, you can write a linter in any language
with a binding to tree-sitter!  Think of all the things you can
recommend to people writing code in your language.  Maybe there's an
unused variable, or style guide for naming identifers, redundant
conditional expressions and so on.  I have yet to do this myself, so
stay tuned for a future blog post!

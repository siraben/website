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
[Imp](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html),
a simple imperative language, and you can get the source code
[here](https://github.com/siraben/tree-sitter-imp).

This post was inspired by my research in improving the developer
experience for
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
This is how to set up a tree-sitter project.r
### Writing the grammar
#### Expressions
First we follow the grammar for expressions given in the chapter.
Here it is for reference.

```
a := nat
   | id
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

The easiest things to handle are numbers and variables.  We can add
the following rules:

```javascript
id: $ => /[a-z]+/,
nat: $ => /[0-9]+/,
```

This corresponds to the tree-sitter grammar

```javascript
program: $ => $.aexp,
aexp: $ => choice(
    /[0-9]+/,
    /[a-z]+/,
    seq($.aexp,'+',$.aexp),
    seq($.aexp,'-',$.aexp),
    seq($.aexp,'*',$.aexp),
    seq('(',$.aexp,')'),
),
```

#### Defining precedence and associativity
Let's try to compile it!  Here's what tree-sitter outputs:

```
Unresolved conflict for symbol sequence:

  aexp  '+'  aexp  •  '+'  …

Possible interpretations:

  1:  (aexp  aexp  '+'  aexp)  •  '+'  …
  2:  aexp  '+'  (aexp  aexp  •  '+'  aexp)

Possible resolutions:

  1:  Specify a left or right associativity in `aexp`
  2:  Add a conflict for these rules: `aexp`
```

Tree-sitter immediately tells that our rules are _ambiguous_, that is,
the same sequence of tokens can have different parse trees.  We don't
want to be ambiguous when writing code!  Let's make everything
left-associative:

```javascript
program: $ => $.aexp,
aexp: $ => choice(
    /[0-9]+/,
    /[a-z]+/,
    prec.left(1,seq($.aexp,'+',$.aexp)),
    prec.left(1,seq($.aexp,'-',$.aexp)),
    prec.left(1,seq($.aexp,'*',$.aexp)),
    seq('(',$.aexp,')'),
),
```

However, something's not quite right when we parse `1*2-3*4`:

<center><img src="/assets/parse.svg" alt="Parse tree for 1*2-3*4"/></center>

It's being parsed as `(1*2-3)*4`, which is clearly a different
interpretation!  We can fix this by specfiying `prec.left(2,...)` for
`*`.  The resulting parse tree we get is what we want.

<center><img src="/assets/parse-correct.svg" alt="Parse tree for 1*2-3*4"/></center>

Note that in many real language specs, the precedence of binary
operators is given, so it becomes pretty routine to figure out the
associativity and precedence to specify.

#### Boolean expressions and statements
The grammars for boolean expressions and statements are similar, and
can be found in the accompanying [repository](https://github.com/siraben/tree-sitter-imp/blob/master/grammar.js).

### Testing the grammar
Phew, so now we have a grammar that tree-sitter compiles.  How do we
actually run it?  The tree-sitter CLI has two subcommands to help out
with this, `tree-sitter parse` and `tree-sitter test`.  The `parse`
subcommand takes a path to a file and parses it with the current
grammar, printing the parse tree to stdout.  The `test` subcommand
runs a suite of tests defined in a very simple syntax:

```
===
skip statement
===
skip
---

(program
  (stmt
    (skip)))
```

The rows of equal signs denote the name of the test, followed by the
program to parse, then a line of dashes followed by the expected parse
tree.

When we run `tree-sitter test`, we get a check if a test passed and a
cross if it failed, complete with a diff showing the expected
vs. actual parse tree:

<div><pre><code>tests:
    ✗ <span style="color: #aa0000">skip</span>
    ✓ <span style="color: #00aa00">assignment</span>
    ✓ <span style="color: #00aa00">prec</span>
    ✓ <span style="color: #00aa00">prog</span>

1 failure:

<span style="color: #00aa00">expected</span> / <span style="color: #aa0000">actual</span>

  1. skip:

    (program
      (stmt
<span style="color: #aa0000">        (seq
          (stmt
            (skip))
          (stmt
            (skip)))))</span>
<span style="color: #00aa00">        (skip)))</span>
</code></pre></div>

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

Tree-sitter's [syntax
highlighting](https://tree-sitter.github.io/tree-sitter/syntax-highlighting#queries)
is based on queries.  Importantly, we need to assign highlight names
to different nodes in the tree.  We only need the following 5 lines
for this simple language.  The square brackets indicate alternations,
that is, if any of the nodes in the tree match an item in the list,
then assign the given capture name (prefixed with `@`) to it.

```scheme
[ "while" "end" "if" "then" "else" "do" ] @keyword
[ "*" "+" "-" "=" ":=" "~" ] @operator
(comment) @comment
(num) @number
(id) @variable.builtin
```

Here's an Imp program that computes factorial of `x` and places the
result in `y`.

```
// Compute factorial
z := x;
y := 1;
while ~(z = 0) do
  y := y * z;
  z := z - 1;
end
```

And here is what `tree-sitter highlight --html` gives

<div><pre><code><span style='font-style: italic;color: #8a8a8a'>// Compute factorial</span>
<span style='font-weight: bold;'>z</span> <span style='font-weight: bold;color: #4e4e4e'>:=</span> <span style='font-weight: bold;'>x</span>;
<span style='font-weight: bold;'>y</span> <span style='font-weight: bold;color: #4e4e4e'>:=</span> <span style='font-weight: bold;color: #875f00'>1</span>;
<span style='color: #5f00d7'>while</span> <span style='font-weight: bold;color: #4e4e4e'>~</span>(<span style='font-weight: bold;'>z</span> <span style='font-weight: bold;color: #4e4e4e'>=</span> <span style='font-weight: bold;color: #875f00'>0</span>) <span style='color: #5f00d7'>do</span>
 <span style='font-weight: bold;'>y</span> <span style='font-weight: bold;color: #4e4e4e'>:=</span> <span style='font-weight: bold;'>y</span> <span style='font-weight: bold;color: #4e4e4e'>*</span> <span style='font-weight: bold;'>z</span>;
 <span style='font-weight: bold;'>z</span> <span style='font-weight: bold;color: #4e4e4e'>:=</span> <span style='font-weight: bold;'>z</span> <span style='font-weight: bold;color: #4e4e4e'>-</span> <span style='font-weight: bold;color: #875f00'>1</span>;
<span style='color: #5f00d7'>end</span></code></pre></div>

Not bad!  Operators, keywords, numbers and identifiers are clearly
highlighted, and the comment being grayed out and italicized makes the
code more readable.

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

### Highlighting redundant statements

```scheme
;; Redundant assignment
((asgn name: _ @left _ @right)
 (#eq? @left @right))

;; Redundant if
(if condition: _ @c consequent: _ @l alternative: _ @r
 (#eq? @l @r)) @redundant_if
```

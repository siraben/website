---
layout: post
title: How to write a linter using tree-sitter in an hour
tags:
- parsing
- tree-sitter
- linting
date: 2022-03-22 11:35 -0500
---
This is a continuation of my last post on [how to write a tree-sitter
grammar in an
afternoon](https://siraben.dev/2022/03/01/tree-sitter.html).  Building
on the grammar we wrote, now we're going to write a linter for
[Imp](https://softwarefoundations.cis.upenn.edu/lf-current/Imp.html),
and it's even easier!  The final result clocks in less than 60 SLOC
and can be found [here](https://github.com/siraben/ts-lint-example).

Recall that tree-sitter is an _incremental_ parser generator.  That
is, you give it a description of the grammar of your programming
language and it spits out a parser in C that creates a syntax tree
based on the rules you specified.  What's notable about tree sitter is
that it is [resilient in the presence of syntax
errors][tree-sitter-errors], and it being incremental means the parser
is fast enough to reparse the file on every keystroke, only changing
the parts of the tree as needed.

[tree-sitter-errors]: https://news.ycombinator.com/item?id=24494756

Specifically, we'll write a program that suggests simplification of
assignments and some conditional constructs.  First I'll describe the
tree-sitter query language with some examples, then show how a little
bit of JavaScript can let us manipulate the results programmatically.
You can get the code in this post [here](https://github.com/siraben/ts-lint-example).
Ready?  Set?  Go!

**Note:** There are many [language
bindings](https://tree-sitter.github.io/tree-sitter/#language-bindings)
that let you work with tree-sitter parsers using the respective
language's FFI.  I've used only two to date, the Rust and the
JavaScript bindings, and from my brief experience, the JavaScript
bindings are much more usable.  When using the Rust bindings the
lifetime and mutability restrictions make abstraction more difficult,
especially for a non-critical program such as a linter.

## Tree-sitter queries
Tree-stter has a builtin [query
language](https://tree-sitter.github.io/tree-sitter/using-parsers#pattern-matching-with-queries)
that lets you write queries to match parts of the AST of interest.
Think of it as pattern matching, but you don't need to handle every
case of a syntactical construct.

### Query syntax
Tree-sitter queries are written as a series of one or more patterns in
an [S-expression](https://en.wikipedia.org/wiki/S-expression) syntax.
We first match on a node's type (corresponding to a name of a node in
the grammar file), then possibly the types of the children of the node
as well.  After each pattern, write `@m` (or any other valid variable
name) so you can refer to the matched node later.

Our running example will be some Python code.

```python
def factorial(n):
  return 1 if n == 0 else (n * (1 * 1)) * factorial(n - 1)
```

Let's match all expressions involving binary operators.

```scheme
(binary_operator) @m
```

<div><pre><code><span>def factorial(n):</span>
<span>  return 1 if n == 0 else <span style="color: blue;">(</span><span style="color: blue;">n * (</span><span style="color: blue;">1 * 1</span><span style="color: blue;">)</span><span style="color: blue;">) * factorial(</span><span style="color: blue;">n - 1</span><span style="color: blue;">)</span></span></code></pre></div>

Tree-sitter lets us specify what the children should be.  So we
can match all binary expressions involving at least one integer:

```scheme
(binary_operator (integer)) @m
```

<div><pre><code><span>def factorial(n):</span>
<span>  return 1 if n == 0 else (n * (<span style="color: blue;">1 * 1</span>)) * factorial(<span style="color: blue;">n - 1</span>)</span></code></pre></div>

Or match all binary expressions involving two integers:

```scheme
(binary_operator (integer) (integer)) @m
```

<div><pre><code><span>def factorial(n):</span>
<span>  return 1 if n == 0 else (n * (<span style="color: blue;">1 * 1</span>)) * factorial(n - 1)</span></code></pre></div>

Try playing around with queries in the
[playground](https://tree-sitter.github.io/tree-sitter/playground).

### Capturing nodes
You can also assign _capture names_ to nodes that you match, letting
you refer to them later by name.  This is useful because in the
running example, suppose we wanted to capture the left and right
integer arguments to a binary operator, labeling them `a` and `b`
respectively.  Then our query would look like this, and tree-sitter
would highlight the matches accordingly.

<div><pre><code><span>(binary_operator (integer) <span style="color: blue;">@a</span> (integer) <span style="color: chocolate;">@b</span>) <span style="color: green;">@m</span></span></code></pre></div>

<div><pre><code><span>def factorial(n):</span>
<span>  return 1 if n == 0 else (n * (<span style="color: blue;">1</span><span style="color: green;"> * </span><span style="color: chocolate;">1</span>)) * factorial(n - 1)</span></code></pre></div>

### Predicates
The tree-sitter query language also lets you specify additional
constraints on matches.  For instance, we can match on binary
expressions where the left-hand side is `n`, which now gets
highlighted in blue.  The underscore `_` lets us match any node.

<div><pre><code><span>((binary_operator _ <span style="color: blue;">@a</span> _ <span style="color: chocolate;">@b</span>) (#eq? <span style="color: blue;">@a</span> n)) <span style="color: green;">@m</span></span></code></pre></div>

<div><pre><code><span>def factorial(n):</span>
<span>  return 1 if n == 0 else (<span style="color: blue;">n</span><span style="color: green;"> </span><span style="color: chocolate;">*</span><span style="color: green;"> </span><span style="color: chocolate;">(1 * 1)</span>) * factorial(<span style="color: blue;">n</span><span style="color: green;"> </span><span style="color: chocolate;">-</span><span style="color: green;"> </span><span style="color: chocolate;">1</span>)</span></code></pre></div>

## Writing the linter
Now we have the basic parts out of the way, we can get to writing a
linter!  Instead of Python, we'll continue working with Imp.  Note
that it's easy to adapt this linter for any language with a
tree-sitter grammar.  Imp also has a much simpler semantics than
Python so we can just focus on "obviously correct" lints rather than
worry about suggestions changing program behavior.

We can start with a basic `package.json`:

```json
{
  "name": "imp-lint",
  "type": "module",
  "version": "1.0.0",
  "description": "Linter for Imp",
  "main": "index.js",
  "scripts": {
    "lint": "node index.js"
  },
  "author": "Ben Siraphob",
  "license": "MIT",
  "devDependencies": {
    "tree-sitter": "^0.20.0",
    "tree-sitter-imp": "github:siraben/tree-sitter-imp"
  }
}
```

Then `npm install` to install the dependencies.  We'll write our code
in `index.js` then we can call our linter by running `npm run lint <file>`.

### Imports and setup
Nothing fancy here, just the Parser class from the tree-sitter library
and our language definition `Imp` (discussed in my last blog post), and
a library to read from the filesystem.

```javascript
import Parser from "tree-sitter";
import Imp from "tree-sitter-imp";
import { readFileSync } from "fs";

const { Query } = Parser;
const parser = new Parser();
parser.setLanguage(Imp);

const args = process.argv.slice(2);

if (args.length != 1) {
  console.error("Usage: npm run lint <file to lint>");
  process.exit(1);
}

// Load the file passed as an argument
const sourceCode = readFileSync(args[0], "utf8");
```

### Creating the parse tree
We then create the parser, set the language to `Imp` and run the
parser on our source code to get out a syntax tree.

```javascript
const parser = new Parser();
parser.setLanguage(Imp);

// Load the file passed as an argument
const tree = parser.parse(sourceCode);
```

If we have the following file:

<div><pre><code><span style="font-weight: bold">x</span> <span style="font-weight: bold; color: #4e4e4e">:=</span> <span style="font-weight: bold">x</span> <span style="font-weight: bold; color: #4e4e4e">+</span> <span style="font-weight: bold; color: #875f00">1</span></code></pre></div>

The corresponding output from `console.log(tree.rootNode.toString())`
would be:

```
(program (stmt (asgn name: (id) (plus (id) (num)))))
```

### Identifying queries of interest
That was some preliminary work.  Now let's see what queries would be
interesting to run over more realistic Imp programs.  Say we have:

<div><pre><code><span style="font-weight: bold">z</span> <span style="font-weight: bold; color: #4e4e4e">:=</span> <span style="font-weight: bold">x</span>;
<span style="font-weight: bold">y</span> <span style="font-weight: bold; color: #4e4e4e">:=</span> <span style="font-weight: bold; color: #875f00">1</span>;
<span style="font-weight: bold">y</span> <span style="font-weight: bold; color: #4e4e4e">:=</span> <span style="font-weight: bold">y</span>;
<span style="color: #5f00d7">while</span> <span style="font-weight: bold; color: #4e4e4e">~</span>(<span style="font-weight: bold">z</span> <span style="font-weight: bold; color: #4e4e4e">=</span> <span style="font-weight: bold; color: #875f00">0</span>) <span style="color: #5f00d7">do</span>
  <span style="font-weight: bold">y</span> <span style="font-weight: bold; color: #4e4e4e">:=</span> <span style="font-weight: bold">y</span> <span style="font-weight: bold; color: #4e4e4e">*</span> <span style="font-weight: bold">z</span>;
  <span style="font-weight: bold">z</span> <span style="font-weight: bold; color: #4e4e4e">:=</span> <span style="font-weight: bold">z</span> <span style="font-weight: bold; color: #4e4e4e">-</span> <span style="font-weight: bold; color: #875f00">1</span>;
  <span style="font-weight: bold">x</span> <span style="font-weight: bold; color: #4e4e4e">:=</span> <span style="font-weight: bold">x</span>;
<span style="color: #5f00d7">end</span>;
<span style="font-weight: bold">x</span> <span style="font-weight: bold; color: #4e4e4e">:=</span> <span style="font-weight: bold">x</span>;
<span style="color: #5f00d7">if</span> <span style="font-weight: bold">x</span> <span style="font-weight: bold; color: #4e4e4e">=</span> <span style="font-weight: bold">y</span> <span style="color: #5f00d7">then</span> <span style="font-weight: bold">x</span> <span style="font-weight: bold; color: #4e4e4e">:=</span> <span style="font-weight: bold; color: #875f00">1</span> <span style="color: #5f00d7">else</span> <span style="font-weight: bold">x</span> <span style="font-weight: bold; color: #4e4e4e">:=</span> <span style="font-weight: bold; color: #875f00">1</span> <span style="color: #5f00d7">end</span></code></pre></div>

There's some redundancies for sure!  We can tell the user about
assignments such as `x := x` which are a no-op, and that last `if`
statement certainly looks redundant since both branches are the same
statement.

It's simple to create a Query object in JavaScript and run it over the
root node.

```javascript
const redundantQuery = new Query(
  Imp,
  "((asgn name: (id) @left _ @right) (#eq? @left @right)) @redundantAsgn"
);

console.log(redundantQuery.captures(tree.rootNode));
```

This is what we get:

```javascript
[
  {
    name: 'redundantAsgn',
    node: AsgnNode {
      type: asgn,
      startPosition: {row: 2, column: 0},
      endPosition: {row: 2, column: 6},
      childCount: 3,
    }
  },
  {
    name: 'left',
    node: IdNode {
      type: id,
      startPosition: {row: 2, column: 0},
      endPosition: {row: 2, column: 1},
      childCount: 0,
    }
  },
  // etc...
]
```

Ok, that's a lot of detail!  Notice that every capture name was
reported along with what type of node matched and the start and end of
the match.  Some tools might want this information, but for us it's
enough to report only the start of the match and the text that the
match corresponded to:

```javascript
// Given a raw list of captures, extract the row, column and text.
function formatCaptures(tree, captures) {
  return captures.map((c) => {
    const node = c.node;
    delete c.node;
    c.text = tree.getText(node);
    c.row = node.startPosition.row;
    c.column = node.startPosition.column;
    return c;
  });
}
```

Now we get something more concise:

```javascript
[
  { name: 'redundantAsgn', text: 'y := y', row: 2, column: 0 },
  { name: 'left', text: 'y', row: 2, column: 0 },
  { name: 'right', text: 'y', row: 2, column: 5 },
  { name: 'redundantAsgn', text: 'x := x', row: 6, column: 2 },
  { name: 'left', text: 'x', row: 6, column: 2 },
  { name: 'right', text: 'x', row: 6, column: 7 },
  { name: 'redundantAsgn', text: 'x := x', row: 8, column: 0 },
  { name: 'left', text: 'x', row: 8, column: 0 },
  { name: 'right', text: 'x', row: 8, column: 5 }
]
```

And of course, it's trivial to filter out the captures corresponding
to a given name:

```javascript
// Get the captures corresponding to a capture name
function capturesByName(tree, query, name) {
  return formatCaptures(
    tree,
    query.captures(tree.rootNode).filter((x) => x.name == name)
  ).map((x) => {
    delete x.name;
    return x;
  });
}
```

Passing `tree`, `redundantQuery` and `"redundantAsgn"` to
`capturesByName`, we get:

```javascript
[
  { text: 'y := y', row: 2, column: 0 },
  { text: 'x := x', row: 6, column: 2 },
  { text: 'x := x', row: 8, column: 0 }
]
```

Now you can process these objects however you like.  Note
that tree-sitter uses zero-based indexing for the rows and columns,
and you might want to offset it by one so users can locate it in their
text editor.  Here's a simple approach:

```javascript
// Lint the tree with a given message, query and match name
function lint(tree, msg, query, name) {
  console.log(msg);
  console.log(capturesByName(tree, query, name));
}

lint(tree, "Redundant assignments:", redundantQuery, "redundantAsgn");
```

We get the output:

```
Redundant assignments:
[
  { text: 'y := y', row: 2, column: 0 },
  { text: 'x := x', row: 6, column: 2 },
  { text: 'x := x', row: 8, column: 0 }
]
```

As a bonus, we can reuse our existing code for new queries!  Here's a
couple:

- Redundant if
```scheme
((if condition: _ @c consequent: _ @l alternative: _ @r)
 (#eq? @l @r)) @redundantIf
```

- Addition with 0
```scheme
((plus (num) @n) (#eq? @n 0)) @addzero
```

Here are some exercises to try:

- Recognize while loops containing only a `skip` statement
- Recognize constant arithmetic and boolean expressions
- Recognize unused variables (those that only appear on the left-hand
  side of an assignment)

## Final thoughts and challenges
To appreciate it more, think about what we would have done had we not
used tree-sitter.  The process might have gone something like this:

1. Write the parser and generate an AST in a given language or parser
   generator
2. Annotate the AST with location information from the source file
3. Traverse the AST looking for matches of interest
4. Report them to the user

Note that there are several steps were things could go wrong or block
us later.  If we wrote the parser, say in Haskell using
[megaparsec](https://hackage.haskell.org/package/megaparsec), we would
have not been able to recover the rows and columns of the syntax
elements (or painfully write an abstract data type with annotations).
And even worse, what happens when the user supplies syntactically
invalid input?  Some parser generators based on GLR parsing such as
[Bison](https://www.gnu.org/software/bison/manual/html_node/Error-Recovery.html)
allow for error recovery, but then we'd need to define a custom
`error` token and come up with ad-hoc logic for dealing with it.

Tree-sitter separates these design choices into orthogonal ones.  A
tree-sitter grammar is easy to write and reusable in any language with
a C FFI.  The error recovery logic is pervasive yet unwritten, and the
resulting AST is annotated with locations and can be easily
pattern-matched over with queries.

Should we throw tree-sitter at every problem involving parsing?  No!
There are certainly some areas where we need syntax trees without
error nodes, and sometimes the incremental parsing is not necessary.
For instance, if we're working with a build farm, we don't want to
build package definitions with syntax errors!

Beyond linting, tree-sitter also has found applications in
GitHub's [search-based code navigation][gh-code-search] which also
makes use of the query language to [annotate the AST with
tags][ast-tags].

[gh-code-search]: https://dl.acm.org/doi/pdf/10.1145/3487019.3487022
[ast-tags]: https://tree-sitter.github.io/tree-sitter/code-navigation-systems

---
layout: post
title: Creating a game with Biwascheme
---

If you don't know about MIT's SICP course (available on
[OpenCourseWare](https://www.youtube.com/watch?v=2Op3QLzMgSY&list=PLE18841CABEA24090)),
you should. Even though it's intended for undergraduates with little
or no experience to programming, this isn't your typical computer
science course. It uses MIT/GNU Scheme, a dialect of Lisp still around
today, and even though the lectures are from 1986 pratically all the
code examples still work.

I read about the [Biwascheme](www.biwascheme.org) Scheme interpreter
in JavaScript and was immediately hooked. Better yet, Biwascheme
offers interoperability with JS, allowing you invoke functions such as
"setAttribute", timers, even dynamically add HTML elements such as
buttons and text.

Over the course of an even or so I created a game which I dub _Ben's
Brownie Brewery_, the whole thing is written in Biwascheme, and was
heavily inspired by Cookie Clicker. It's released under the GNU GPLv3
license and you can play it
**[here](https://siraben.github.io/brownies/)**. It's _very_ alpha and
still contains a couple of bugs, nevertheless, it's perfectly
playable.

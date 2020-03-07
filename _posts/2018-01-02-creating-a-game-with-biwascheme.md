---
layout: post
title: Creating a game with Biwascheme
tags: [scheme, javascript]
---

If you don't know about MIT's SICP course (available on
[OpenCourseWare](https://www.youtube.com/watch?v=2Op3QLzMgSY&list=PLE18841CABEA24090)),
you should. Even though it's intended for undergraduates with little
or no experience to programming, this isn't your typical computer
science course. It uses MIT/GNU Scheme, a dialect of Lisp still around
today, and even though the lectures are from 1986 pratically all the
code examples still work.  It covers everything from recursion,
higher-order functions, the functional, symbolic, generic,
object-oriented (read: message-oriented), meta programming paradigms,
thanks to Lisp, and even builds a Prolog-like language, interpreter
and compiler towards the end of the book!

I read about the [Biwascheme](www.biwascheme.org) Scheme interpreter
in JavaScript and was immediately hooked. Better yet, Biwascheme
offers interoperability with JS, allowing you invoke functions such as
"setAttribute", timers, even dynamically add HTML elements such as
buttons and text.

Over the course of an even or so I created a game which I dub _Ben's
Brownie Brewery_, the whole thing is written in Biwascheme, and is
essentially a stripped down version of cookie clicker. It's released
under the GNU GPLv3 license and you can play it
[here](https://siraben.github.io/brownies/). Just to show, as a proof
of concept, that Scheme could be used on the web for dynamic content.

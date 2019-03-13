# lean-perfectoid-spaces
A formalization of the concept of a perfectoid space in the Lean formal proof verification system.

By [Kevin Buzzard](http://wwwf.imperial.ac.uk/~buzzard/), [Johan Commelin](http://math.commelin.net/), and [Patrick Massot](https://www.math.u-psud.fr/~pmassot/).

### Definition of a perfectoid space in the Lean Programming Language.

This is a project whose first goal is to create a type in a certain
computer language. The language is Lean, which is some version of
dependent type theory. Dependent type theory is another foundation for
mathematics, and in this type theory you can do all the things that
mathematicians are used to doing in ZFC set theory.

The name of the type we're constructing is `perfectoid_space`. One could
define a *perfectoid space* to be a term of this type. Hence any
computer program which outputs a term of this type could be said to be a
program which computed a perfectoid space. Our initial goal is to finish
formalising the definition, and after that one could imagine proving
basic results about perfectoid spaces within Lean. Is this sort of thing
feasible? We don't know. We think so though, and we're not really sure if
anyone has tried this sort of thing before. Let's find out!

### Getting it working.

This project is not yet finished. It usually compiles, or mostly
compiles, with Lean 3.4.2 and Mathlib HEAD. Usually there are some sorries but no errors. When there are no sorries, we will be finished.

A brief guide to compiling the library on your machine:

1) Install Lean and Visual Studio Code following, for example, [this guide](https://github.com/leanprover-community/mathlib/blob/master/docs/elan.md)

2) Clone the project:

```
git clone git@github.com:leanprover-community/lean-perfectoid-spaces.git
```

This will create a new directory `lean-perfectoid-spaces`.

3) Build the project by typing `leanpkg build` in the `lean-perfectoid-spaces` directory.

4) Open the `lean-perfectoid-spaces` directory in Visual Studio Code.

5) That's it.

If you are considering contributing then you will want to use an IDE, and the two standard ones for Lean are VS Code and emacs. Instructions for setting these editors up for Lean are [here](https://leanprover.github.io/reference/using_lean.html#using-lean-with-vscode) in the Lean reference manual.

### I am a mathematician. How do I learn Lean?

You can read [theorem proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/). Do note however that this whole thing is all very beta at the minute. I think [Tom Hales describes it best](https://jiggerwit.wordpress.com/2018/04/14/the-architecture-of-proof-assistants/).

### Chat

You're welcome to ask questions at

Chat : https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Perfectoid.20spaces


### Useful references

[Brian Conrad's learning seminar](http://math.stanford.edu/~conrad/Perfseminar/).

[Scholze etale cohomology of diamonds (ArXiv)](https://arxiv.org/abs/1709.07343).

[Fontaine's text for Seminaire Bourbaki](http://www.bourbaki.ens.fr/TEXTES/1057.pdf).

[Torsten Wedhorn's notes on adic spaces](http://wwwf.imperial.ac.uk/~buzzard/docs/AdicSpaces.pdf).

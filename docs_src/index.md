---
title: Perfectoid Spaces in Lean
---
# What is it about?

We explained Peter Scholze's definition of perfectoid spaces to
computers, using the [Lean theorem prover](https://leanprover.github.io/), 
mainly developed at [Microsoft Research](https://www.microsoft.com/en-us/research/) 
by [Leonardo de Moura](https://leodemoura.github.io/).
Building on earlier work by many people, starting from first
principles, we arrived at
```lean
-- We fix a prime number p
parameter (p : primes)

/-- A perfectoid ring is a Huber ring that is complete, uniform,
that has a pseudo-uniformizer whose p-th power divides p in the power bounded subring,
and such that Frobenius is a surjection on the reduction modulo p.-/
structure perfectoid_ring (R : Type) [Huber_ring R] extends Tate_ring R : Prop :=
(complete  : is_complete_hausdorff R)
(uniform   : is_uniform R)
(ramified  : ∃ ϖ : pseudo_uniformizer R, ϖ^p ∣ p in Rᵒ)
(Frobenius : surjective (Frob Rᵒ∕p))

/-
CLVRS ("complete locally valued ringed space") is a category
whose objects are topological spaces with a sheaf of complete topological rings
and an equivalence class of valuation on each stalk, whose support is the unique
maximal ideal of the stalk; in Wedhorn's notes this category is called 𝒱.
A perfectoid space is an object of CLVRS which is locally isomorphic to Spa(A) with
A a perfectoid ring. Note however that CLVRS is a full subcategory of the category
`PreValuedRingedSpace` of topological spaces equipped with a presheaf of topological
rings and a valuation on each stalk, so the isomorphism can be checked in
PreValuedRingedSpace instead, which is what we do.
-/

/-- Condition for an object of CLVRS to be perfectoid: every point should have an open
neighbourhood isomorphic to Spa(A) for some perfectoid ring A.-/
def is_perfectoid (X : CLVRS) : Prop :=
∀ x : X, ∃ (U : opens X) (A : Huber_pair) [perfectoid_ring A],
  (x ∈ U) ∧ (Spa A ≊ U)

/-- The category of perfectoid spaces.-/
def PerfectoidSpace := {X : CLVRS // is_perfectoid X}

end

```
You can read more explanations about [how to read this code](how-to-read-lean.html).

Starting from first principles means every definition and every lemma
needed to make sense of the above lines has been explained to
computers, by us or [other people](https://github.com/leanprover-community/mathlib/graphs/contributors), and checked by computers.

Each node in the following graph is a definition or statement used
directly or indirectly in the definition of perfectoid spaces, or in the
proofs of the required lemmas. Each edge is a use. There are more than
3000 nodes and 30000 edges. The spatial layout and cluster coloring were
computed independently by [Gephi](https://gephi.org/), using tools
[Force atlas 2](https://github.com/gephi/gephi/wiki/Force-Atlas-2) and
[modularity](https://github.com/gephi/gephi/wiki/Modularity).
[![Perfectoid definition graph](images/perfectoid_graph_small.png)](images/perfectoid_graph.png)
Labels were added by hand. The big star is the definition of perfectoid
spaces. All other nodes have a size depending on how many nodes use
them. You can play with the [gephi source](perfectoid.gephi). 
Note that, although the definition of perfectoid spaces is
there, we are still working on making the project more beautiful, so
the graph may be not perfectly faithful to its current state.

In order to get a legible graph, we had to remove some foundational nodes
like the definition of equality, existential quantifier, or powerset
(none of which is a primitive concept in dependent type theory with
inductive constructions, the mathematical foundations used by Lean).
These nodes were related to too many others, and prevented computation
of meaningful spatial layout or modularity classes. We lost of bit of
mathematics unity display, but the middle of the graph still features
many different colors in the same zone, corresponding to topological
algebra (groups or rings equipped with a topology or uniform structure
compatible with their algebraic operations). The red class at the bottom
is labelled "Filters", but it also includes quite a bit of naive set
theory (somewhat orphaned by the removal of the powerset node). The word
lattice should be understood in the order relation theoretic sense, not
its group theoretic sense.

If you want to explore the project code interactively, you can read our
[installation instructions](install.html).

### Chat

You're welcome to ask questions at the [Zulip chat](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Perfectoid.20spaces).

## I am a mathematician. How do I learn Lean?

You can read [theorem proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/). Do note however that this whole thing is all very beta at the minute. We think [Tom Hales describes it best](https://jiggerwit.wordpress.com/2018/04/14/the-architecture-of-proof-assistants/).


## Useful references

[Brian Conrad's learning seminar](http://math.stanford.edu/~conrad/Perfseminar/).

[Scholze etale cohomology of diamonds (ArXiv)](https://arxiv.org/abs/1709.07343).

[Fontaine's text for Seminaire Bourbaki](http://www.bourbaki.ens.fr/TEXTES/1057.pdf).

[Torsten Wedhorn's notes on adic spaces](http://wwwf.imperial.ac.uk/~buzzard/docs/AdicSpaces.pdf).

# What is it about?

We explained Peter Scholze's definition of perfectoid spaces to
computers, using the [Lean theorem prover](https://leanprover.github.io/), mainly developped by
[Leonardo de Moura](https://leodemoura.github.io/).
Building on earlier work by many people, starting from first
principles, we arrived at
```lean
parameter (p : ℕ)
variable [is_prime p]

/-- A perfectoid ring, following Fontaine Sem. Bourbaki-/
structure perfectoid_ring (R : Type) [Huber_ring R] extends Tate_ring R : Prop :=
(complete : is_complete_hausdorff R)
(uniform  : is_uniform R)
(ramified : ∃ ϖ : pseudo_uniformizer R, (ϖ^p : Rᵒ) ∣ p)
(Frob     : ∀ a : Rᵒ, ∃ b : Rᵒ, (p : Rᵒ) ∣ (b^p - a : Rᵒ))

-- CLVRS ("complete locally valued ringed space") is a category
-- whose objects are topological spaces with a presheaf of topological rings
-- and an equivalence class of valuation on each stalk; a perfectoid space is locally
-- isomorphic to Spa(A) with A a perfectoid ring, and the isomorphism can be checked 
-- in CLVRS.

/-- Condition for an object of CLVRS to be perfectoid: every point should have an
open neighbourhood isomorphic to Spa(A) for some perfectoid ring A. -/
def is_perfectoid (X : CLVRS) : Prop :=
∀ x : X, ∃ (U : opens X) (A : Huber_pair) [perfectoid_ring A],
  (x ∈ U) ∧ (Spa A ≊ U)
```
You can read more explanations about [how to read this code](how-to-read-lean.html)

Starting from first principles means every definition and every lemma
needed to make sense of the above lines have been explained to
computers, by us or [other people](https://github.com/leanprover-community/mathlib/graphs/contributors), and checked by computers.

Each node in the following graph is a definition or statement used
directly or indirectly in the definition of perfectoid spaces, or in the
proofs of the required lemmas. Each edge is a use. There are more than
3000 nodes and 30000 edges. The spatial layout and cluster coloring was
computed by [Gephi](https://gephi.org/).
![Perfectoid definition graph](images/perfectoid_graph.png)
Labels were added by hand. The big star is the definition of perfectoid
spaces. All other nodes have a size depending on how many nodes use
them. You can play with the [gephi source](perfectoid.gephi). 
Note that, although the definition of perfectoid spaces is
there, we are still working on making the project more beautiful, so
the graph maybe be not perfectly faithful to its current state.

If you want to explore the project interactively, you can read our
[installation instruction](install.html)

### Chat

You're welcome to ask questions at the [Zulip chat](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Perfectoid.20spaces)

## I am a mathematician. How do I learn Lean?

You can read [theorem proving in Lean](https://leanprover.github.io/theorem_proving_in_lean/). Do note however that this whole thing is all very beta at the minute. We think [Tom Hales describes it best](https://jiggerwit.wordpress.com/2018/04/14/the-architecture-of-proof-assistants/).


## Useful references

[Brian Conrad's learning seminar](http://math.stanford.edu/~conrad/Perfseminar/).

[Scholze etale cohomology of diamonds (ArXiv)](https://arxiv.org/abs/1709.07343).

[Fontaine's text for Seminaire Bourbaki](http://www.bourbaki.ens.fr/TEXTES/1057.pdf).

[Torsten Wedhorn's notes on adic spaces](http://wwwf.imperial.ac.uk/~buzzard/docs/AdicSpaces.pdf).

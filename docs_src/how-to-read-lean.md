# How to read Lean

On this page we explain how to read the file
[`perfectoid_space.lean`](https://github.com/leanprover-community/lean-perfectoid-spaces/blob/master/src/perfectoid_space.lean)
step by step.

We start with the first 5 lines
```lean
-- We import definitions of adic_space, preadic_space, Huber_pair, etc
import prime
import adic_space
import Tate_ring
import power_bounded
```
These lines import other definitions, theorems, notation, etc… from other files in the library.
This import is transitive, so this will automatically import a large part of the library
(on algebra, topology, etc, and ultimately basic logic).

```lean
section
-- notation for the power bounded subring
local postfix `ᵒ` : 66 := power_bounded_subring
```
We start a section, and then setup notation for the power bounded subring.
Because a postfix `ᵒ` is also useful as notation for other concepts,
we choose to make this notation local to this file, instead of global notation for every file that imports this file.

```lean
open power_bounded_subring topological_space function
```
This block opens three namespaces.
Namespaces exist to avoid naming conflicts.
As an example, there are functions `nat.add` and `int.add`,
that define the addition on natural numbers and integers respectively.
Thus we have two functions `add`, one in the namespace `nat`, and the other in the namespace `int`.

By opening a namespace, we don't have to write down the namespace prefix when referring to a definition or lemma in the namespace.
For example, `topological_space.opens X` is the type of all open subsets of `X`.
But because we open the namespace `topological_space`, we can simply write `opens X` later on in the file.

```lean
parameter (p : Prime)
```
Once and for all (in this file) we fix a prime number `p`.

```lean
structure perfectoid_ring (R : Type) [Huber_ring R] extends Tate_ring R : Prop :=
(complete  : is_complete_hausdorff R)
(uniform   : is_uniform R)
(ramified  : ∃ ϖ : pseudo_uniformizer R, ϖ^p ∣ p in Rᵒ)
(Frobenius : bijective (Frob Rᵒ∕p))
```
In this block there are a lot of things going on.
First of all, this block defines a predicate, because it is of the form `structure something : Prop := something`.
Indeed, `Prop` is the type of propositions: theorems, lemmas, properties, predicates…
The predicate in question is `perfectoid_ring`, and it is a predicate for Huber rings.
(Technically, it defines the predicate for types `R` endowed with the structure of a Huber ring.)
The predicate extends another predicate, namely `Tate_ring R`,
which is defined in one of the files that were imported at the top of this file.
In addition to the conditions put forth in the predicate `Tate_ring`,
this predicate imposes four new conditions:
 * it requires `R` to be complete and Hausdorff
 * `R` should be uniform
 * it asks for the existence of a pseudo-uniformizer, whose `p`-th power divides `p` in the subring `Rᵒ`
 * and finally it requires the quotient of the power-bounded subring modulo `p` to be a perfect ring.

Note the (for mathematicians) funny notation in the last two conditions.
Because Lean is based on type theory, it uses `:` in places where a mathematician would usually write `∈`.
In condition `ramified`, we ask for the existence of a term `ϖ` of type `pseudo_uniformizer R`.

Note also that the notation of the universal and existential quantifier use a `,` where some mathematicians would write a `:`.
Because the `:` already has a very fundamental meaning, we don't write
`∃ (x : X) : condition_on_x` to mean “there exists an `x` such that condition-on-`x`”
but instead we write `∃ (x : X), condition_on_x`.

```lean
-- CLVRS ("complete locally valued ringed space") is a category
-- whose objects are topological spaces with a presheaf of topological rings
-- and an equivalence class of valuation on each stalk; a perfectoid space is locally
-- isomorphic to Spa(A) with A a perfectoid ring, and the isomorphism can be checked in CLVRS.
```
This comment explains the symbol `CLVRS` that is used in the rest of the file.
It is a category that is defined in one of the imported files.

```lean
/-- Condition for an object of CLVRS to be perfectoid: every point should have an open
neighbourhood isomorphic to Spa(A) for some perfectoid ring A.-/
def is_perfectoid (X : CLVRS) : Prop :=
∀ x : X, ∃ (U : opens X) (A : Huber_pair) [perfectoid_ring A],
(x ∈ U) ∧ (Spa A ≊ U)
```
We now define a predicate on objects of the category `CVLRS`.
Such an object is perfectoid if every point has an open neighbourhood that is isomorphic to the adic spectrum of a perfectoid ring.

Finally we define the type of perfectoid spaces.
It is the type of all objects of `CLVRS` that satisfy the predicate `is_perfectoid`.
```lean
/-- The category of perfectoid spaces.-/
def PerfectoidSpace := {X : CLVRS // is_perfectoid X}

end
```

import topology.order
import group_theory.quotient_group
import valuation.canonical

/- Valuation Spectrum (Spv)

The API for the valuation spectrum of a commutative ring. Normally defined as
"the equivalence classes of valuations", there are set-theoretic issues.
These issues are easily solved by noting that two valuations are equivalent
if and only if they induce the same preorder on R, where the preorder
attacted to a valuation sends (r,s) to v r ≤ v s.

Our definition of Spv is currently the predicates which come from a
valuation. There is another approach though: Prop 2.20 (p16) of
https://homepages.uni-regensburg.de/~maf55605/contin_valuation.pdf
classifies the relations which come from valuations as those satisfying
some axioms. See also Wedhorn 4.7.
TODO(jmc): This observation is also somewhere in Huber. But I currently don't
have the paper at hand.

Here's why such a theorem must exist: given a relation coming from a valuation,
we can reconstruct the support of the valuation (v r ≤ v 0), the relation on
R / support coming from `on_quot v`, the relation on Frac(R/supp) coming from
`on_frac v`, the things of valuation 1 in this field, and hence the value group
of the valuation. The induced canonical valuation is a valuation we seek. This
argument only uses a finite number of facts about the inequality, and so the
theorem is that an inequality comes from a valuation if and only if these facts
are satisfied.

-/

universes u u₀ u₁ u₂ u₃

/-- Valuation spectrum of a ring. -/
-- Note that the valuation takes values in a group in the same universe as R.
-- This is to avoid "set-theoretic issues".
definition Spv (R : Type u₀) [comm_ring R] :=
{ineq : R → R → Prop // ∃ {Γ₀ : Type u₀} [linear_ordered_comm_group Γ₀],
 by exactI ∃ (v : valuation R Γ₀), ∀ r s : R, v r ≤ v s ↔ ineq r s}

variables {R : Type u₀} [comm_ring R] {v : Spv R}

local notation r `≤[`v`]` s := v.1 r s

/- Spv R is morally a quotient, so we start by giving it a quotient-like interface -/
namespace Spv
open valuation

variables {Γ  : Type u}  [linear_ordered_comm_group Γ]
variables {Γ₁ : Type u₁} [linear_ordered_comm_group Γ₁]
variables {Γ₂ : Type u₂} [linear_ordered_comm_group Γ₂]

-- The work is embedded here with `canonical_valuation_is_equiv v` etc.
-- The canonical valuation attached to v lives in R's universe.
/-- The constructor for a term of type Spv R given an arbitrary valuation -/
definition mk (v : valuation R Γ) : Spv R :=
⟨λ r s, v r ≤ v s,
  ⟨value_group v, by apply_instance, canonical_valuation v, canonical_valuation_is_equiv v⟩⟩

@[simp] lemma mk_val (v : valuation R Γ) : (mk v).val = λ r s, v r ≤ v s := rfl

/-- The value group attached to a term of type Spv R -/
definition out_Γ (v : Spv R) : Type u₀ := classical.some v.2

noncomputable instance (v : Spv R) : linear_ordered_comm_group (out_Γ v) :=
classical.some $ classical.some_spec v.2

/-- An explicit valuation attached to a term of type Spv R -/
noncomputable definition out (v : Spv R) : valuation R (out_Γ v) :=
classical.some $ classical.some_spec $ classical.some_spec v.2

@[simp] lemma mk_out {v : Spv R} : mk (out v) = v :=
begin
  rcases v with ⟨ineq, hv⟩,
  rw subtype.ext,
  ext,
  exact classical.some_spec (classical.some_spec (classical.some_spec hv)) _ _,
end

lemma out_mk (v : valuation R Γ) : (out (mk v)).is_equiv v :=
classical.some_spec (classical.some_spec (classical.some_spec (mk v).2))

noncomputable def lift {X}
  (f : Π ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group Γ₀], valuation R Γ₀ → X) (v : Spv R) : X :=
f (out v)

/-- The computation principle for Spv -/
theorem lift_eq {X}
  (f₀ : Π ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group Γ₀], valuation R Γ₀ → X)
  (f : Π ⦃Γ : Type u⦄ [linear_ordered_comm_group Γ], valuation R Γ → X)
  (v : valuation R Γ)
  (h : ∀ ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group Γ₀] (v₀ : valuation R Γ₀),
    v₀.is_equiv v → f₀ v₀ = f v) :
  lift f₀ (mk v) = f v :=
h _ (out_mk v)

/-- Prop-valued version of computation principle for Spv -/
theorem lift_eq'
  (f₀ : Π ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group Γ₀], valuation R Γ₀ → Prop)
  (f : Π ⦃Γ : Type u⦄ [linear_ordered_comm_group Γ], valuation R Γ → Prop)
  (v : valuation R Γ)
  (h : ∀ ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group Γ₀] (v₀ : valuation R Γ₀),
    v₀.is_equiv v → (f₀ v₀ ↔ f v)) :
  lift f₀ (mk v) ↔ f v :=
h _ (out_mk v)

lemma exists_rep (v : Spv R) :
  ∃ {Γ₀ : Type u₀} [linear_ordered_comm_group Γ₀], by exactI ∃ (v₀ : valuation R Γ₀),
  mk v₀ = v :=
⟨out_Γ v, infer_instance, out v, mk_out⟩

lemma sound {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} (h : v₁.is_equiv v₂) : mk v₁ = mk v₂ :=
begin
  apply subtype.val_injective,
  ext r s,
  apply h,
end

lemma is_equiv_of_eq_mk {v₁ : valuation R Γ₁} {v₂ : valuation R Γ₂} (h : mk v₁ = mk v₂) :
  v₁.is_equiv v₂ :=
begin
  intros r s,
  have := congr_arg subtype.val h,
  replace := congr this (rfl : r = r),
  replace := congr this (rfl : s = s),
  simp at this,
  simp [this],
end

noncomputable instance : has_coe_to_fun (Spv R) :=
{ F := λ v, R → with_zero (out_Γ v),
  coe := λ v, ((out v) : R → with_zero (out_Γ v)) }

section

@[simp] lemma map_zero : v 0 = 0 := valuation.map_zero _
@[simp] lemma map_one  : v 1 = 1 := valuation.map_one _
@[simp] lemma map_mul  : ∀ x y, v (x * y) = v x * v y := valuation.map_mul _
@[simp] lemma map_add  : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y := valuation.map_add _

end

/-- The open sets generating the topology of Spv R, see Wedhorn 4.1.-/
definition basic_open (r s : R) : set (Spv R) :=
{v | v r ≤ v s ∧ v s ≠ 0}

instance : topological_space (Spv R) :=
topological_space.generate_from {U : set (Spv R) | ∃ r s : R, U = basic_open r s}

lemma mk_mem_basic_open {r s : R} (v : valuation R Γ) :
  mk v ∈ basic_open r s ↔ v r ≤ v s ∧ v s ≠ 0 :=
begin
  apply and_congr,
  { apply out_mk, },
  { apply (out_mk v).ne_zero, },
end

end Spv


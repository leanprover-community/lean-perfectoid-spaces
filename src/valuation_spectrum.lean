import topology.order
import group_theory.quotient_group
import valuation.canonical

/-!
# Valuation Spectrum (Spv)

The API for the valuation spectrum of a commutative ring. Normally defined as
"the equivalence classes of valuations", there are set-theoretic issues.
These issues are easily solved by noting that two valuations are equivalent
if and only if they induce the same preorder on R, where the preorder
attached to a valuation sends (r,s) to v r ≤ v s.

## Implementation details

Our definition of Spv is currently the predicates which come from a
valuation. There is another approach though:
In the proof of Prop 2.2 of “Continuous Valuations” by R. Huber,
the relations that come from a valuations are classified as thoe satisfying some axioms.
See also Wedhorn 4.7.
-/

universes u u₀ u₁ u₂ u₃

local attribute [instance, priority 0] classical.DLO

/-- Valuation spectrum of a ring. -/
-- Note that the valuation takes values in a group in the same universe as R.
-- This is to avoid "set-theoretic issues".
definition Spv (R : Type u₀) [comm_ring R] :=
{ineq : R → R → Prop // ∃ {Γ₀ : Type u₀} [linear_ordered_comm_group_with_zero Γ₀],
 by exactI ∃ (v : valuation R Γ₀), ∀ r s : R, v r ≤ v s ↔ ineq r s}

variables {R : Type u₀} [comm_ring R] {v : Spv R}

local notation r `≤[`v`]` s := v.1 r s

/- Spv R is morally a quotient, so we start by giving it a quotient-like interface -/
namespace Spv
open valuation

variables {Γ₀  : Type u}   [linear_ordered_comm_group_with_zero Γ₀]
variables {Γ'₀ : Type u₁}  [linear_ordered_comm_group_with_zero Γ'₀]
variables {Γ''₀ : Type u₂} [linear_ordered_comm_group_with_zero Γ''₀]

-- The work is embedded here with `canonical_valuation_is_equiv v` etc.
-- The canonical valuation attached to v lives in R's universe.
/-- The equivalence class of a valuation. -/
definition mk (v : valuation R Γ₀) : Spv R :=
⟨λ r s, v r ≤ v s,
  ⟨value_monoid v, by apply_instance, canonical_valuation v, canonical_valuation_is_equiv v⟩⟩

@[simp] lemma mk_val (v : valuation R Γ₀) : (mk v).val = λ r s, v r ≤ v s := rfl

/-- The value group attached to a term of type Spv R -/
definition out_Γ₀ (v : Spv R) : Type u₀ := classical.some v.2

/-- The value group attached to a term of type Spv R
is a linearly ordered commutative group with zero. -/
noncomputable instance (v : Spv R) : linear_ordered_comm_group_with_zero (out_Γ₀ v) :=
classical.some $ classical.some_spec v.2

/-- An explicit representative of an equivalence class of valuations (a term of type Spv R). -/
noncomputable definition out (v : Spv R) : valuation R (out_Γ₀ v) :=
classical.some $ classical.some_spec $ classical.some_spec v.2

@[simp] lemma mk_out {v : Spv R} : mk (out v) = v :=
begin
  rcases v with ⟨ineq, hv⟩,
  rw subtype.ext,
  ext,
  exact classical.some_spec (classical.some_spec (classical.some_spec hv)) _ _,
end

/-- The explicit representative of the equivalence class of a valuation v is equivalent to v. -/
lemma out_mk (v : valuation R Γ₀) : (out (mk v)).is_equiv v :=
classical.some_spec (classical.some_spec (classical.some_spec (mk v).2))

/-- A function defined on all valuations of R descends to Spv R. -/
noncomputable def lift {X}
  (f : Π ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group_with_zero Γ₀], valuation R Γ₀ → X) (v : Spv R) : X :=
f (out v)

/-- The computation principle for Spv:
If a function is constant on equivalence classes of valuations,
then it descends to a well-defined function on Spv R.-/
theorem lift_eq {X}
  (f₀ : Π ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group_with_zero Γ₀], valuation R Γ₀ → X)
  (f : Π ⦃Γ₀ : Type u⦄ [linear_ordered_comm_group_with_zero Γ₀], valuation R Γ₀ → X)
  (v : valuation R Γ₀)
  (h : ∀ ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group_with_zero Γ₀] (v₀ : valuation R Γ₀),
    v₀.is_equiv v → f₀ v₀ = f v) :
  lift f₀ (mk v) = f v :=
h _ (out_mk v)

/-- Prop-valued version of the computation principle for Spv:
If a predicate is constant on equivalence classes of valuations,
then it descends to a well-defined predicate on Spv R.-/
theorem lift_eq'
  (f₀ : Π ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group_with_zero Γ₀], valuation R Γ₀ → Prop)
  (f : Π ⦃Γ₀ : Type u⦄ [linear_ordered_comm_group_with_zero Γ₀], valuation R Γ₀ → Prop)
  (v : valuation R Γ₀)
  (h : ∀ ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group_with_zero Γ₀] (v₀ : valuation R Γ₀),
    v₀.is_equiv v → (f₀ v₀ ↔ f v)) :
  lift f₀ (mk v) ↔ f v :=
h _ (out_mk v)

/-- For every term of Spv R, there exists a valuation representing it.-/
lemma exists_rep (v : Spv R) :
  ∃ {Γ₀ : Type u₀} [linear_ordered_comm_group_with_zero Γ₀], by exactI ∃ (v₀ : valuation R Γ₀),
  mk v₀ = v :=
⟨out_Γ₀ v, infer_instance, out v, mk_out⟩

/-- The quotient map that sends a valuation to its equivalence class is sound:
it sends equivalent valuations to the same class. -/
lemma sound {v₁ : valuation R Γ'₀} {v₂ : valuation R Γ''₀} (h : v₁.is_equiv v₂) : mk v₁ = mk v₂ :=
begin
  apply subtype.val_injective,
  ext r s,
  apply h,
end

/-- The induction principle for Spv.-/
lemma induction_on (v : Spv R) (P : Spv R → Prop)
  (h : Π ⦃Γ₀ : Type u₀⦄ [linear_ordered_comm_group_with_zero Γ₀] (v : valuation R Γ₀), P (Spv.mk v)) :
  P v :=
begin
  rw ← @mk_out _ _ v,
  apply h
end

/-- If two valuations are mapped to the same term of Spv R, then they are equivalent. -/
lemma is_equiv_of_eq_mk {v₁ : valuation R Γ'₀} {v₂ : valuation R Γ''₀} (h : mk v₁ = mk v₂) :
  v₁.is_equiv v₂ :=
begin
  intros r s,
  have := congr_arg subtype.val h,
  replace := congr this (rfl : r = r),
  replace := congr this (rfl : s = s),
  simp at this,
  simp [this],
end

@[ext]
lemma ext (v₁ v₂ : Spv R) (h : (Spv.out v₁).is_equiv (Spv.out v₂)) :
  v₁ = v₂ :=
by simpa only [Spv.mk_out] using Spv.sound h

lemma ext_iff  {v₁ v₂ : Spv R} :
  v₁ = v₂ ↔ ((Spv.out v₁).is_equiv (Spv.out v₂)) :=
⟨λ h, Spv.is_equiv_of_eq_mk (by simpa only [Spv.mk_out] using h), Spv.ext _ _⟩

/-- A coercion that allows to treat an element of Spv(R) as a function,
by picking a random representative of the equivalence class of valuations. -/
noncomputable instance : has_coe_to_fun (Spv R) :=
{ F := λ v, R → out_Γ₀ v,
  coe := λ v, (out v : R → out_Γ₀ v) }

section

@[simp] lemma map_zero : v 0 = 0 := valuation.map_zero _
@[simp] lemma map_one  : v 1 = 1 := valuation.map_one _
@[simp] lemma map_mul  : ∀ x y, v (x * y) = v x * v y := valuation.map_mul _
@[simp] lemma map_add  : ∀ x y, v (x + y) ≤ max (v x) (v y) := valuation.map_add _

end

section supp

/--The support of an equivalence class of valuations.-/
noncomputable def supp (v : Spv R) := v.out.supp

/--The support of an equivalence class of valuations is equal to the
support of any of its representatives.-/
@[simp] lemma supp_mk (v : valuation R Γ₀) : (mk v).supp = v.supp :=
(out_mk v).supp_eq

end supp

section comap
variables {S : Type*} [comm_ring S] {T : Type*} [comm_ring T]

/--The pullback of an equivalence class of valuations
along a ring homomorphism.-/
noncomputable def comap (f : R → S) [is_ring_hom f] : Spv S → Spv R :=
lift $ λ Γ₀ _ v, by exactI Spv.mk (v.comap f)

/--The pullpack of an equivalence class of valuations
is the equivalence class of the pullback of any of its representatives.-/
lemma comap_mk (f : R → S) [is_ring_hom f] (v : valuation S Γ₀) :
  comap f (mk v) = mk (v.comap f) :=
begin
  delta comap, rw lift_eq,
  intros Γ₀ _ v h, resetI,
  apply sound,
  exact is_equiv.comap f h
end

/--The pullback along the identity is the identity.-/
lemma comap_id_apply (v : Spv R) : comap (id : R → R) v = v :=
begin
  apply induction_on v, clear v,
  intros Γ₀ _ v, resetI,
  rw [comap_mk, valuation.comap_id],
end

/--The pullback along the identity is the identity.-/
@[simp] lemma comap_id : comap (id : R → R) = id :=
funext $ comap_id_apply

/--The pullback along a composition is the composition of the pullback maps.-/
@[simp] lemma comap_comp_apply (g : S → T) (f : R → S) [is_ring_hom g] [is_ring_hom f] (v : Spv T):
  comap (g ∘ f) v = comap f (comap g v) :=
begin
  apply induction_on v, clear v,
  intros Γ₀ _ v, resetI,
  rw [comap_mk, comap_mk, comap_mk, valuation.comap_comp],
end

/--The pullback along a composition is the composition of the pullback maps.-/
@[simp] lemma comap_comp (g : S → T) (f : R → S) [is_ring_hom g] [is_ring_hom f] :
  comap (g ∘ f) = comap f ∘ comap g :=
funext $ comap_comp_apply g f

/--The support of the pullback of an equivalence class of valuations
is the pullback (as ideal) of the support.-/
lemma supp_comap (f : R → S) [is_ring_hom f] (v : Spv S) :
  (v.comap f).supp = v.supp.comap f :=
begin
  apply induction_on v, clear v,
  intros Γ₀ _ v, resetI,
  rw [comap_mk, supp_mk, supp_mk, valuation.comap_supp],
end

/--An element is contained in the support of the pullback of an equivalence
class of valuations if and only if its image is contained in the support.-/
lemma mem_supp_comap (f : R → S) [is_ring_hom f] (v : Spv S) (r : R) :
  r ∈ (v.comap f).supp ↔ f r ∈ v.supp :=
by { rw supp_comap, exact iff.rfl }

end comap

/-- The open sets generating the topology of Spv R. See [Wedhorn, Def 4.1].-/
definition basic_open (r s : R) : set (Spv R) :=
{v | v r ≤ v s ∧ v s ≠ 0}

/-- The topology on the valuation spectrum of a ring. -/
instance : topological_space (Spv R) :=
topological_space.generate_from {U : set (Spv R) | ∃ r s : R, U = basic_open r s}

lemma mk_mem_basic_open {r s : R} (v : valuation R Γ₀) :
  mk v ∈ basic_open r s ↔ v r ≤ v s ∧ v s ≠ 0 :=
begin
  apply and_congr,
  { apply out_mk, },
  { apply (out_mk v).ne_zero, },
end

end Spv

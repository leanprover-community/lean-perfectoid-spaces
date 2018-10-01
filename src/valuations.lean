import algebra.group_power
import set_theory.cardinal
import ring_theory.ideals
import data.finsupp
import group_theory.quotient_group
import tactic.tidy
import for_mathlib.ideals
import for_mathlib.linear_ordered_comm_group

universes u₁ u₂ u₃ -- v is used for valuations

namespace valuation

class is_valuation {R : Type u₁} [comm_ring R] {Γ : Type u₂} [linear_ordered_comm_group Γ]
  (v : R → with_zero Γ) : Prop :=
(map_zero : v 0 = 0)
(map_one  : v 1 = 1)
(map_mul  : ∀ x y, v (x * y) = v x * v y)
(map_add  : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y)

end valuation

def valuation (R : Type u₁) [comm_ring R] (Γ : Type u₂) [linear_ordered_comm_group Γ] :=
{ v : R → with_zero Γ // valuation.is_valuation v }

instance (R : Type u₁) [comm_ring R] (Γ : Type u₂) [linear_ordered_comm_group Γ] :
has_coe_to_fun (valuation R Γ) := { F := λ _, R → with_zero Γ, coe := subtype.val}

namespace valuation

variables {R : Type u₁} [comm_ring R]
variables {Γ : Type u₂} [linear_ordered_comm_group Γ]
variables (v : valuation R Γ) {x y z : R}

@[simp] lemma map_zero : v 0 = 0 := v.property.map_zero
@[simp] lemma map_one  : v 1 = 1 := v.property.map_one
@[simp] lemma map_mul  : ∀ x y, v (x * y) = v x * v y := v.property.map_mul
@[simp] lemma map_add  : ∀ x y, v (x + y) ≤ v x ∨ v (x + y) ≤ v y := v.property.map_add

theorem map_unit (h : x * y = 1) : option.is_some (v x) :=
begin
  have h1 := v.map_mul x y,
  rw [h, map_one v] at h1,
  cases (v x),
  { exfalso,
    exact option.no_confusion h1 },
  { constructor }
end

theorem map_neg_one : v (-1) = 1 :=
begin
  have h1 : (-1 : R) * (-1) = 1 := by simp,
  have h2 := map_unit v h1,
  have h3 := map_mul v (-1) (-1),
  rw [option.is_some_iff_exists] at h2,
  cases h2 with x h,
  change v (-1) = some x at h,
  show v (-1) = 1,
  rw h at h3 ⊢,
  congr,
  rw [h1, map_one v] at h3,
  replace h3 := eq.symm (option.some.inj h3),
  have h4 : x^2 = 1 := by simpa [pow_two] using h3,
  exact linear_ordered_comm_group.eq_one_of_pow_eq_one h4
end

section

variables {Γ₁ : Type u₂} [linear_ordered_comm_group Γ₁]
variables {Γ₂ : Type u₃} [linear_ordered_comm_group Γ₂] 
variables {v₁ : R → with_zero Γ₁} {v₂ : R → with_zero Γ₂}
variables {ψ : Γ₁ → Γ₂}
variables (H12 : ∀ r, with_zero.map ψ (v₁ r) = v₂ r)
variables (Hle : ∀ g h : Γ₁, g ≤ h ↔ ψ g ≤ ψ h)
include H12 Hle

theorem le_of_le (r s : R) : v₁ r ≤ v₁ s ↔ v₂ r ≤ v₂ s :=
begin
  rw ←H12 r, rw ←H12 s,
  cases hr : (v₁ r) with g;
  cases hs : (v₁ s) with h; try {simp},
  exact Hle g h
end 

theorem valuation_of_valuation [is_group_hom ψ]
  (Hiψ : function.injective ψ)
  (H : is_valuation v₂) :
is_valuation v₁ :=
{ map_zero := begin
    show v₁ 0 = 0,
    have H0 : v₂ 0 = 0 := H.map_zero,
    rw ←H12 0 at H0,
    change with_zero.map ψ (v₁ 0) = 0 at H0,
    cases h : v₁ 0, refl,
    exfalso,
    rw h at H0,
    revert H0,
    exact dec_trivial
  end,
map_one := begin
    show v₁ 1 = 1,
    have H0 : v₂ 1 = 1 := H.map_one,
    rw ←H12 1 at H0,
    cases h : v₁ 1,
    { change v₁ 1 = 0 at h, rw h at H0,
      simpa only [with_zero.map_zero] using H0 },
    { rw h at H0,
      change some (ψ val) = some 1 at H0,
      congr,
      apply Hiψ,
      rw [option.some_inj.1 H0, is_group_hom.one ψ] }
  end,
map_mul := begin
    intros r s,
    apply with_zero.map_inj Hiψ,
    rw [H12 (r * s), H.map_mul, ←H12 r, ←H12 s],
    symmetry,
    exact with_zero.map_mul _ _ _,
  end,
map_add := begin
    intros r s,
    cases is_valuation.map_add v₂ r s,
    { left,
      rw [←H12 r, ←H12 (r+s)] at h,
      rwa with_zero.map_le Hle },
    { right,
      rw [←H12 s, ←H12 (r+s)] at h,
      rwa with_zero.map_le Hle }
  end }

end

def map {S : Type u₃} [comm_ring S] (f : S → R) [is_ring_hom f] : valuation S Γ :=
{ val := v ∘ f,
  property :=
  { map_zero := by simp [is_ring_hom.map_zero f],
    map_one  := by simp [is_ring_hom.map_one f],
    map_mul  := by simp [is_ring_hom.map_mul f],
    map_add  := by simp [is_ring_hom.map_add f] } }

section trivial
variables (S : set R) [is_prime_ideal S] [decidable_pred S]

def trivial : valuation R Γ :=
{ val := λ x, if x ∈ S then 0 else 1,
  property :=
  { map_zero := if_pos (is_submodule.zero_ R S),
    map_one  := if_neg is_proper_ideal.one_not_mem,
    map_mul  := λ x y, begin
        split_ifs with hxy hx hy; try {simp}; exfalso,
        { cases is_prime_ideal.mem_or_mem_of_mul_mem hxy with h' h',
          { exact hx h' },
          { exact h h' } },
        { have H : x * y ∈ S, exact is_ideal.mul_right h,
          exact hxy H },
        { have H : x * y ∈ S, exact is_ideal.mul_right h,
          exact hxy H },
        { have H : x * y ∈ S, exact is_ideal.mul_left h_1,
          exact hxy H }
      end,
    map_add  := λ x y, begin
        split_ifs with hxy hx hy; try {simp};
        try {left; exact le_refl _};
        try {right}; try {exact le_refl _},
        { have hxy' : x + y ∈ S := is_submodule.add_ R h h_1,
          exfalso, exact hxy hxy' }
      end } }

@[simp] lemma trivial_val : (trivial S).val = (λ x, if x ∈ S then 0 else 1 : R → (with_zero Γ)) := rfl

end trivial

section supp
open with_zero

def supp : set R := {x | v x = 0}

instance : is_prime_ideal (supp v) :=
{ zero_ := map_zero v,
  add_  := λ x y hx hy, or.cases_on (map_add v x y)
    (λ hxy, le_antisymm (hx ▸ hxy) zero_le)
    (λ hxy, le_antisymm (hy ▸ hxy) zero_le),
  smul  := λ c x hx, calc v (c * x)
                        = v c * v x : map_mul v c x
                    ... = v c * 0 : congr_arg _ hx
                    ... = 0 : mul_zero _,
  ne_univ := λ h, have h1 : (1:R) ∈ supp v, by rw h; trivial,
    have h2 : v 1 = 0 := h1,
    by rw [map_one v] at h2; exact option.no_confusion h2,
  mem_or_mem_of_mul_mem := λ x y hxy, begin
      dsimp [supp] at hxy ⊢,
      change v (x * y) = 0 at hxy,
      rw [map_mul v x y] at hxy,
      exact eq_zero_or_eq_zero_of_mul_eq_zero _ _ hxy
    end }

/-
definition extension_to_integral_domain {α : Type} [linear_ordered_comm_group α]
  {R : Type} [comm_ring R] (f : R → with_zero α) [H : is_valuation f] :
  (comm_ring.quotient R (supp f)) → with_zero α := sorry
-/

end supp

variable (v)

definition value_group := group.closure {a : Γ | ∃ r : R, v r = some a}

definition value_group_v (v : R → with_zero Γ) [is_valuation v] :=
group.closure ({a : Γ | ∃ r : R, v r = some a})

instance : group (value_group v) :=
@subtype.group _ _ (value_group v) (group.closure.is_subgroup {a : Γ | ∃ r : R, v r = some a})

instance valutaion.group_v (v : R → with_zero Γ) [is_valuation v] : group (value_group_v v) :=
  @subtype.group _ _ (value_group_v v) (group.closure.is_subgroup {a : Γ | ∃ r : R, v r = some a})

end valuation

namespace valuation
open quotient_group

variables {R : Type u₁} [comm_ring R] [decidable_eq R]

structure minimal_valuation.parametrized_subgroup (Γ₂ : Type u₂) [linear_ordered_comm_group Γ₂] :=
(Γ : Type u₁)
[grp : comm_group Γ]
(inc : Γ → Γ₂)
[hom : is_group_hom inc]
(inj : function.injective inc)

local attribute [instance] parametrized_subgroup.grp
local attribute [instance] parametrized_subgroup.hom

variables  {Γ₂ : Type u₂} [linear_ordered_comm_group Γ₂]
variables (v₂ : valuation R  Γ₂)

set_option class.instance_max_depth 41
include R v₂
def minimal_value_group : minimal_valuation.parametrized_subgroup Γ₂ :=
begin
  let FG : Type u₁ := multiplicative (R →₀ ℤ), -- free ab group on R
  let φ₀ : R → Γ₂ := λ r, option.get_or_else (v₂ r) 1,
  let φ : FG → Γ₂ := λ f, finsupp.prod f (λ r n,(φ₀ r) ^ n),
  haveI : is_group_hom φ := 
    ⟨λ a b, finsupp.prod_add_index (λ a, rfl) (λ a b₁ b₂, gpow_add (φ₀ a) b₁ b₂)⟩,
  
  exact
  { Γ     :=  quotient (is_group_hom.ker φ),
    inc   :=  lift (is_group_hom.ker φ) φ (λ _,(is_group_hom.mem_ker φ).1),
    hom   := quotient_group.is_group_hom_quotient_lift _ _ _,
    inj   := injective_ker_lift φ }
end

namespace minimal_value_group

def mk (r : R) : (minimal_value_group v₂).Γ :=
begin
  let FG : Type u₁ := multiplicative (R →₀ ℤ), -- free ab group on R
  let φ₀ : R → Γ₂ := λ r, option.get_or_else (v₂ r) 1,
  let φ : FG → Γ₂ := λ f, finsupp.prod f (λ r n,(φ₀ r) ^ n),
  haveI : is_group_hom φ := 
    ⟨λ a b, finsupp.prod_add_index (λ a, rfl) (λ a b₁ b₂, gpow_add (φ₀ a) b₁ b₂)⟩,

  exact quotient_group.mk (finsupp.single r (1 : ℤ))
end

lemma mk_some {r : R} {g : Γ₂} (h : v₂ r = some g) : 
  v₂ r = some ((minimal_value_group v₂).inc (mk v₂ r)) :=
begin
  rw h,
  congr' 1,
  dsimp[minimal_value_group, minimal_value_group.mk],
  rw finsupp.prod_single_index ; finish
end

instance : linear_ordered_comm_group (minimal_value_group v₂).Γ :=
begin
  cases minimal_value_group v₂ with Γ₁ _ ψ _ inj,
  
  letI Γ₁linord : linear_order Γ₁ := 
  { le := λ g h, ψ g ≤ ψ h,
    le_refl := λ _, le_refl _,
    le_trans := λ _ _ _ hab hbc, le_trans hab hbc,
    le_antisymm := λ g h Hgh Hhg, inj $ le_antisymm Hgh Hhg,
    le_total := λ g h, le_total _ _ },
  exact ⟨λ a b H c,
    begin
      change ψ (c * a) ≤ ψ (c * b),
      rw [is_group_hom.mul ψ c b, is_group_hom.mul ψ c a],
      exact linear_ordered_comm_group.mul_le_mul_left H _,
    end⟩
end

end minimal_value_group

definition minimal_valuation.val (r : R) : with_zero ((minimal_value_group v₂).Γ) :=
match v₂ r with 
| some _ := some (minimal_value_group.mk v₂ r)
| 0 := 0
end

namespace minimal_valuation

@[simp] lemma zero {r} (h : v₂ r = 0) : val v₂ r = 0 :=
by simp [val, h]

lemma some {r} {g} (h : v₂ r = some g) : val v₂ r = some (minimal_value_group.mk v₂ r) :=
by simp [val, h]

lemma map (r : R) :
with_zero.map (minimal_value_group v₂).inc (val v₂ r) = v₂ r :=
begin
  destruct (v₂ r),
  { intro h, change v₂ r = 0 at h,
    simp [zero v₂ h, h], },
  { intros g h,
    rw [minimal_value_group.mk_some v₂ h, some v₂ h, with_zero.map_some] },
end

end minimal_valuation

def minimal_valuation : valuation R (minimal_value_group v₂).Γ :=
{ val := minimal_valuation.val v₂,
  property := let Γ₁ := minimal_value_group v₂ in
    valuation_of_valuation (minimal_valuation.map v₂) (λ g h, iff.refl _) Γ₁.inj (v₂.property) }

def minimal_valuation_equiv (r s : R) : (v₂.minimal_valuation :
valuation R (minimal_value_group v₂).Γ) r ≤ (v₂.minimal_valuation : valuation R (minimal_value_group v₂).Γ) s ↔ v₂ r ≤ v₂ s :=
le_of_le (minimal_valuation.map v₂) (λ g h, iff.refl _) r s

end valuation

/- quotes from mathlib (mostly Mario) (all 2018)

Jul03

class is_valuation {α : Type} [linear_ordered_comm_group α]
  {R : Type} [comm_ring R] (f : R → option α) : Prop :=
(map_zero : f 0 = 0)
(map_one  : f 1 = 1)
(map_mul  : ∀ x y, f (x * y) = f x * f y)
(map_add  : ∀ x y, f (x + y) ≤ f x ∨ f (x + y) ≤ f y)

namespace is_valuation 

...

structure valuation (R : Type) [comm_ring R] (α : Type) [Hα : linear_ordered_comm_group α] :=
(f : R → option α)
(Hf : is_valuation f)

...

**All Jul03**

MC: What's wrong, again, with defining Spv as the collection of all valuation relations?
KB: All proofs need an actual valuation
MC: You can define your own version of quot.lift and quot.mk that take valuations
MC: valuation functions that is
[quot.lift is the statement that if I have a function on valuations which is constant
on equiv classes then I can produce a function on Spv]
MC: You only use the relations as inhabitants of the type so that the universe isn't pushed up,
    but all the work uses functions
MC: You will need to prove the computation rule, so it won't be definitional, but otherwise it
    should work smoothly if your API is solid
MC: No equivalence class needed either
MC: quot.mk takes a valuation function and produces an element of Spv
MC: quot.lift takes a function defined on valuation functions and produces a function defined on Spv
KB: So what about proofs which go "Spv(R) is compact. Proof: take an element of Spv(R), call it v or
    f or whatever, and now manipulate f in the following way..."
MC: That's quot.lift
MC: Actually you will want quot.ind as well
["any subset of the quotient type containing the image of quot.mk is everything"]
or equivalently quot.exists_rep
[lemma exists_rep {α : Sort u} {r : α → α → Prop} (q : quot r) : ∃ a : α, (quot.mk r a) = q :=
]
MC: that is, for every element of Spv there is a valuation function that quot.mk's to it
MC: Note it's not actually a function producing valuation functions, it's an exists
MC: if you prove analogues of those theorems for your type, then you have constructed the
    quotient up to isomorphism
MC: This all has a category theoretic interpretation as a coequalizer, and all constructions
    are natural in that category
MC: As opposed to, say, quot.out, which picks an element from an equivalence class
MC: Although in your case if I understand correctly you also have a canonical way to define quot.out
    satisfying some other universal property to do with the ordered group
    where the valuation and ring have to share the same universe.
    You can prove that the universe need not be the same as part of the universal properties
    i.e. Spv.mk takes as input a valuation function  (v : valuation R A) where {R : Type u} and
    {A : Type v} (so it isn't just instantiating the exists)
KB: "If you want to be polymorphic" -- I just want to do maths. I have no idea if I want to be polymorphic.
     If I just want to define a perfectoid space, do I want to be polymorphic?
MC : In lean, you should usually be polymorphic
     at least in contravariant positions (i.e. the inputs should be maximally polymorphic, the output should
      be minimally polymorphic)
     This is why we don't have nat : Type u
     The general rule is to keep types out of classes if at all possible. Lean behaves better when the
     types are given as "alpha" rather than "the type inside v", particularly if you start manipulating
     the functions (adding them, say).
     It is the same things that make the difference between bundled vs unbundled groups. When
     working "internally", i.e. calculations using the monoid structure, it is better for the type
     to be exposed as a variable
-/

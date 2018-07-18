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

where the valuation and ring have to share the same universe
9:37 AM

You can prove that the universe need not be the same as part of the universal properties
9:38 AM

i.e. Spv.mk takes as input a valuation function  (v : valuation R A) where {R : Type u} and {A : Type v} (so it isn't just instantiating the exists)
9:41 AM

"If you want to be polymorphic" -- I just want to do maths. I have no idea if I want to be polymorphic. If I just want to define a perfectoid space, do I want to be polymorphic?
9:46 AM

In lean, you should usually be polymorphic
9:47 AM

at least in contravariant positions (i.e. the inputs should be maximally polymorphic, the output should be minimally polymorphic)
9:47 AM

This is why we don't have nat : Type u
10:41 AM

If I read correctly, you want to have a class is_valuation, and then a structure type valuation made of all functions f satisfying the valuation axioms, i.e., with is_valuation f. What is the advantage of this approach (with typeclass inference) over the more direct approach with a structure type valuation in which you put directly the axioms, and then when you want to work with a valuation you just use (v : valuation R A) (so, getting rid completely of the typeclass is_valuation)?
10:58 AM

The problem is that a valuation is a function from a ring to some totally ordered monoid, and there's an equivalence relation which needs to be taken into account, of the form "these monoids might not be the same, but there's a map from the image of one function to the image of the other which makes lots of things commute". Spv R is the equivalence classes of valuations.
11:22 AM

I understand this. My question is about the beginning of the discussion, with this is_valuation class at the start of your formalization.
11:51 AM

I am not the person to ask, I don't think. I have no understanding of how best to do these things in Lean, that's why I'm floundering around here. I understand the maths perfectly. Let me try and read your messages. Yes we have an inductive prop is_valuation fwhich is a class although I don't know if that's sensible (I think Kenny made it a class so it probably is). We then apparently are supposed to have a type valuation R alpha which is all valuations taking values in alpha; I have no real understanding of why this is needed because I definitely don't care about all valuations taking values in alpha. You mention typeclass inference but I have no idea what should be a class because whilst I now understand what typeclass inference is and how to use it when other people have made the typeclasses, I am still extremely unclear myself about which of my own objects should be typeclasses. You now suggest I could be making a structure type valuation -- would this take alpha as part of the structure? I think we used to have that; Johan maybe mentioned it, and Mario said that alpha should not be part of the structure. Is A the totally ordered monoid? The only reason we have is_valuation is that someone else wrote it. I say again -- I completely understand the mathematics I want to do; I am extremely foggy about how to do it in Lean in the sense that I can see several ways and simply do not possess the toolkit necessary to work out the best way. There's my attempt to answer your question in full. At the end of the day I want Spv R to be the equivalence classes of valuations on R, and I have no idea whether valuation or valuations or is_valuation or structure or class or what is the best approach. I would happily be told explicitly what to do.
11:52 AM

Am I right in thinking that Mario basically told me a way of doing it above, and you are suggesting another way?
11:57 AM

I don't think Sebastien is suggesting anything different from what I recommended (using augmented functions)
11:59 AM

    I have no real understanding of why this is needed because I definitely don't care about all valuations taking values in alpha.

The general rule is to keep types out of classes if at all possible. Lean behaves better when the types are given as "alpha" rather than "the type inside v", particularly if you start manipulating the functions (adding them, say)
12:00 PM

Although you want to deal with "the collection of all valuations" (which is what Spv is for), when doing a concrete calculation you will have a fixed alpha with respect to which to do your monoid algebra stuff
1:25 PM

        I have no real understanding of why this is needed because I definitely don't care about all valuations taking values in alpha.

    The general rule is to keep types out of classes if at all possible. Lean behaves better when the types are given as "alpha" rather than "the type inside v", particularly if you start manipulating the functions (adding them, say)

Hmmm, can you be more precise about how Lean would misbehave? Because it seems "mathematically natural/convenient" to make alpha part of the structure, instead of a parameter.
1:33 PM

it is the same things that make the difference between bundled vs unbundled groups. When working "internally", i.e. calculations using the monoid structure, it is better for the type to be exposed as a variable
1:34 PM

When working externally, there is already the type Spv to do this
1:35 PM

Also, there is a universe issue for the ZFC diehards
1:49 PM

If I understand Sebastien correctly, then he suggesting to just merge is_valuation fand valuation R Gamma into one class. In other words, substitute the fields of is_valuation for the Hf field in valuation.
3:15 PM

    it is the same things that make the difference between bundled vs unbundled groups. When working "internally", i.e. calculations using the monoid structure, it is better for the type to be exposed as a variable

I am still not up to speed with notation. "bundled" means alpha is part of the structure? exposed type means it's not?
9:05 PM

    If I understand Sebastien correctly, then he suggesting to just merge is_valuation fand valuation R Gamma into one class. In other words, substitute the fields of is_valuation for the Hf field in valuation.

Exactly (except that I don't think it should be a class, only a structure, as typeclass inference will not help you there and you want to put several valuations on the same object).


-/


import algebra.group_power
import set_theory.cardinal
import ring_theory.ideals
import for_mathlib.subrel 
import for_mathlib.ideals 
-- import for_mathlib.quotient_ring -- might be best to use what Chris did!
import group_theory.subgroup

class linear_ordered_comm_monoid (α : Type*)
    extends comm_monoid α, linear_order α :=
(mul_le_mul_left : ∀ {a b : α}, a ≤ b → ∀ c : α, c * a ≤ c * b)

class linear_ordered_comm_group (α : Type*)
    extends comm_group α, linear_order α :=
(mul_le_mul_left : ∀ {a b : α}, a ≤ b → ∀ c : α, c * a ≤ c * b)

local infix ^ := monoid.pow

namespace linear_ordered_comm_group

variables {α : Type*} [linear_ordered_comm_group α] {x y z : α}
variables {β : Type*} [linear_ordered_comm_group β]

class is_hom (f : α → β) : Prop :=
(Hf : is_group_hom f)
(Hord : ∀ {a b : α}, a ≤ b → f a ≤ f b)

instance hom_is_group_hom (f : α → β) [H : is_hom f] : is_group_hom f := H.Hf

structure equiv extends equiv α β :=
(is_hom : is_hom to_fun)

lemma mul_le_mul_right (H : x ≤ y) : ∀ z : α, x * z ≤ y * z :=
λ z, mul_comm z x ▸ mul_comm z y ▸ mul_le_mul_left H z

lemma one_le_mul_of_one_le_of_one_le (Hx : 1 ≤ x) (Hy : 1 ≤ y) : 1 ≤ x * y :=
have h1 : x * 1 ≤ x * y, from mul_le_mul_left Hy x,
have h2 : x ≤ x * y, by rwa mul_one x at h1,
le_trans Hx h2

lemma one_le_pow_of_one_le {n : ℕ} (H : 1 ≤ x) : 1 ≤ x^n :=
begin
  induction n with n ih,
  { exact le_refl 1 },
  { exact one_le_mul_of_one_le_of_one_le H ih }
end

lemma mul_le_one_of_le_one_of_le_one (Hx : x ≤ 1) (Hy : y ≤ 1) : x * y ≤ 1 :=
have h1 : x * y ≤ x * 1, from mul_le_mul_left Hy x,
have h2 : x * y ≤ x, by rwa mul_one x at h1,
le_trans h2 Hx

lemma pow_le_one_of_le_one {n : ℕ} (H : x ≤ 1) : x^n ≤ 1 :=
begin
  induction n with n ih,
  { exact le_refl 1 },
  { exact mul_le_one_of_le_one_of_le_one H ih }
end

/-- Wedhorn Remark 1.6 (3) -/
lemma eq_one_of_pow_eq_one {n : ℕ} (H : x ^ nat.succ n = 1) : x = 1 :=
begin
  induction n with n ih,
  { unfold monoid.pow at H;simpa using H },
  { cases le_total x 1,
    { have h1 := mul_le_mul_right h (x ^ nat.succ n),
      dsimp [monoid.pow] at H h1,
      rw [H, one_mul] at h1,
      have h2 := pow_le_one_of_le_one h,
      exact ih (le_antisymm h2 h1) },
    { have h1 := mul_le_mul_right h (x ^ nat.succ n),
      dsimp [monoid.pow] at H h1,
      rw [H, one_mul] at h1,
      have h2 := one_le_pow_of_one_le h,
      exact ih (le_antisymm h1 h2) } }
end

lemma inv_le_one_of_one_le (H : 1 ≤ x) : x⁻¹ ≤ 1 :=
by simpa using mul_le_mul_left H (x⁻¹)

lemma inv_le_inv_of_le (H : x ≤ y) : y⁻¹ ≤ x⁻¹ :=
have h1 : _ := mul_le_mul_left H (x⁻¹ * y⁻¹),
by rwa [inv_mul_cancel_right, mul_comm x⁻¹, inv_mul_cancel_right] at h1

lemma le_one_or_inv_le_one (x : α) : x ≤ 1 ∨ x⁻¹ ≤ 1 :=
or.imp id inv_le_one_of_one_le (le_total x 1)

lemma le_or_inv_le_inv (x y : α) : x ≤ y ∨ x⁻¹ ≤ y⁻¹ :=
or.imp id inv_le_inv_of_le (le_total x y)

class is_convex (S : set α) : Prop :=
(one_mem : (1:α) ∈ S)
(mul_mem : ∀ {x y}, x ∈ S → y ∈ S → x * y ∈ S)
(inv_mem : ∀ {x}, x ∈ S → x⁻¹ ∈ S)
(mem_of_between : ∀ {x y}, x ≤ y → y ≤ (1:α) → x ∈ S → y ∈ S)

class is_proper_convex (S : set α) extends is_convex S : Prop :=
(exists_ne : ∃ (x y : α) (hx : x ∈ S) (hy : y ∈ S), x ≠ y)

definition convex_linear_order : linear_order {S : set α // is_convex S} :=
{ le_total := λ ⟨x, hx⟩ ⟨y, hy⟩, classical.by_contradiction $ λ h,
    let ⟨h1, h2⟩ := not_or_distrib.1 h,
        ⟨m, hmx, hmny⟩ := set.not_subset.1 h1,
        ⟨n, hny, hnnx⟩ := set.not_subset.1 h2 in
    begin
      cases le_total m n with hmn hnm,
      { cases le_one_or_inv_le_one n with hn1 hni1,
        { exact hnnx (@@is_convex.mem_of_between _ hx hmn hn1 hmx) },
        { cases le_total m (n⁻¹) with hmni hnim,
          { exact hnnx (inv_inv n ▸ (@@is_convex.inv_mem _ hx $ @@is_convex.mem_of_between _ hx hmni hni1 hmx)) },
          { cases le_one_or_inv_le_one m with hm1 hmi1,
            { exact hmny (@@is_convex.mem_of_between _ hy hnim hm1 $ @@is_convex.inv_mem _ hy hny) },
            { exact hmny (inv_inv m ▸ (@@is_convex.inv_mem _ hy $ @@is_convex.mem_of_between _ hy (inv_le_inv_of_le hmn) hmi1 $ @@is_convex.inv_mem _ hy hny)) } } } },
      { cases le_one_or_inv_le_one m with hm1 hmi1,
        { exact hmny (@@is_convex.mem_of_between _ hy hnm hm1 hny) },
        { cases le_total n (m⁻¹) with hnni hmim,
          { exact hmny (inv_inv m ▸ (@@is_convex.inv_mem _ hy $ @@is_convex.mem_of_between _ hy hnni hmi1 hny)) },
          { cases le_one_or_inv_le_one n with hn1 hni1,
            { exact hnnx (@@is_convex.mem_of_between _ hx hmim hn1 $ @@is_convex.inv_mem _ hx hmx) },
            { exact hnnx (inv_inv n ▸ (@@is_convex.inv_mem _ hx $ @@is_convex.mem_of_between _ hx (inv_le_inv_of_le hnm) hni1 $ @@is_convex.inv_mem _ hx hmx)) } } } }
    end,
  .. subrel.partial_order }

def ker (f : α → β) (hf : is_hom f) : set α :=
{ x | f x = 1 }

theorem ker.is_convex (f : α → β) (hf : is_hom f) : is_convex (ker f hf) :=
{ one_mem := is_group_hom.one f,
  mul_mem := λ x y hx hy, show f (x * y) = 1, by dsimp [ker] at hx hy; rw [(hf.1).mul, hx, hy, mul_one],
  inv_mem := λ x hx, show f x⁻¹ = 1, by dsimp [ker] at hx; rw [@is_group_hom.inv _ _ _ _ f (hf.1) x, hx, one_inv],
  mem_of_between := λ x y hxy hy1 hx, le_antisymm (is_group_hom.one f ▸ is_hom.Hord _ hy1) (hx ▸ is_hom.Hord _ hxy) }

def height (α : Type) [linear_ordered_comm_group α] : cardinal :=
cardinal.mk {S : set α // is_proper_convex S}

namespace extend

def mul : option α → option α → option α
| (some x) (some y) := some (x * y)
| _        _        := none

theorem mul_assoc : ∀ (x y z : option α), mul (mul x y) z = mul x (mul y z)
| (some x) (some y) (some z) := congr_arg some $ _root_.mul_assoc x y z
| (some _) (some _) none     := rfl
| (some _) none     (some z) := rfl
| (some _) none     none     := rfl
| none     (some _) (some z) := rfl
| none     (some _) none     := rfl
| none     none     (some z) := rfl
| none     none     none     := rfl

def one : option α := some 1

def one_mul : ∀ x : option α, mul one x = x
| (some x) := congr_arg some $ _root_.one_mul x
| none     := rfl

def mul_one : ∀ x : option α, mul x one = x
| (some x) := congr_arg some $ _root_.mul_one x
| none     := rfl

def mul_comm : ∀ (x y : option α), mul x y = mul y x
| (some x) (some y) := congr_arg some $ _root_.mul_comm x y
| (some x) none     := rfl
| none     (some _) := rfl
| none     none     := rfl

def le : option α → option α → Prop
| (some x) (some y) := x ≤ y
| (some _) none     := false
| none     _        := true

theorem le_refl : ∀ x : option α, le x x
| (some x) := _root_.le_refl x
| none     := trivial

theorem le_trans : ∀ x y z : option α, le x y → le y z → le x z
| (some x) (some y) (some z) hxy hyz := _root_.le_trans hxy hyz
| (some _) (some _) none     hxy hyz := false.elim hyz
| (some _) none     _        hxy hyz := false.elim hxy
| none     _        _        hxy hyz := trivial

theorem le_antisymm : ∀ x y : option α, le x y → le y x → x = y
| (some x) (some y) hxy hyx := congr_arg some $ _root_.le_antisymm hxy hyx
| (some _) none     hxy hyx := false.elim hxy
| none     (some _) hxy hyx := false.elim hyx
| none     none     hxy hyx := rfl

theorem le_total : ∀ x y : option α, le x y ∨ le y x
| (some x) (some y) := _root_.le_total x y
| none     _        := or.inl trivial
| _        none     := or.inr trivial

theorem mul_le_mul_left : ∀ x y : option α, le x y → ∀ z : option α, le (mul z x) (mul z y)
| (some x) (some y) hxy (some z) := linear_ordered_comm_group.mul_le_mul_left hxy z
| _        _        hxy none     := trivial
| (some _) none     hxy _        := false.elim hxy
| none     _        hxy (some _) := trivial

instance : linear_ordered_comm_monoid (option α) :=
{ mul             := mul,
  mul_assoc       := mul_assoc,
  one             := one,
  one_mul         := one_mul,
  mul_one         := mul_one,
  mul_comm        := mul_comm,
  le              := le,
  le_refl         := le_refl,
  le_trans        := le_trans,
  le_antisymm     := le_antisymm,
  le_total        := le_total,
  mul_le_mul_left := mul_le_mul_left }

instance : has_zero (option α) := ⟨none⟩

theorem zero_mul : ∀ x : option α, 0 * x = 0
| _ := rfl

theorem mul_zero : ∀ x : option α, x * 0 = 0
| (some _) := rfl
| none     := rfl

theorem none_mul : ∀ x : option α, none * x = none := zero_mul
theorem mul_none : ∀ x : option α, x * none = none := mul_zero

theorem eq_zero_or_eq_zero_of_mul_eq_zero : ∀ x y : option α, x * y = 0 → x = 0 ∨ y = 0
| (some x) (some y) hxy := false.elim $ option.no_confusion hxy
| none     _        hxy := or.inl rfl
| _        none     hxy := or.inr rfl

end extend

end linear_ordered_comm_group

structure valuation (R : Type*) [comm_ring R] (Γ : Type*) [linear_ordered_comm_group Γ] :=
(f : R → option Γ)
(map_zero : f 0 = 0)
(map_one  : f 1 = 1)
(map_mul  : ∀ x y, f (x * y) = f x * f y)
(map_add  : ∀ x y, f (x + y) ≤ f x ∨ f (x + y) ≤ f y)

instance (R : Type*) [comm_ring R] (Γ : Type*) [HΓ : linear_ordered_comm_group Γ] :
has_coe_to_fun (valuation R Γ) := { F := λ _,R → option Γ, coe := λ v,v.f}

class is_valuation {α : Type*} [linear_ordered_comm_group α]
  {R : Type*} [comm_ring R] (f : R → option α) : Prop :=
(map_zero : f 0 = 0)
(map_one  : f 1 = 1)
(map_mul  : ∀ x y, f (x * y) = f x * f y)
(map_add  : ∀ x y, f (x + y) ≤ f x ∨ f (x + y) ≤ f y)

namespace is_valuation

variables {α : Type*} [linear_ordered_comm_group α]
variables {R : Type*} [comm_ring R] (f : R → option α)
variables [is_valuation f] {x y z : R}

theorem map_unit : x * y = 1 → option.is_some (f x) :=
begin
  intro h,
  have h1 := map_mul f x y,
  rw [h, map_one f] at h1,
  cases (f x),
  { exfalso,
    exact option.no_confusion h1 },
  { constructor }
end

theorem map_neg_one : f (-1) = 1 :=
begin
  have h1 : (-1 : R) * (-1) = 1 := by simp,
  have h2 := map_unit f h1,
  have h3 := map_mul f (-1) (-1),
  rw [option.is_some_iff_exists] at h2,
  cases h2 with x h,
  rw h at h3 ⊢,
  congr,
  rw [h1, map_one f] at h3,
  replace h3 := eq.symm (option.some.inj h3),
  have h4 : x^2 = 1 := by simpa [monoid.pow] using h3,
  exact linear_ordered_comm_group.eq_one_of_pow_eq_one h4
end

namespace trivial

variables (S : set R) [is_prime_ideal S] [decidable_pred S]

instance : is_valuation (λ x, if x ∈ S then (0 : option α) else 1) :=
{ map_zero := if_pos (is_submodule.zero_ R S),
  map_one  := if_neg is_proper_ideal.one_not_mem,
  map_mul  := λ x y, begin
      by_cases hx : x ∈ S,
      { rw if_pos hx,
        rw linear_ordered_comm_group.extend.zero_mul,
        rw if_pos (is_ideal.mul_right _ hx) },
      { by_cases hy : y ∈ S,
        { rw if_pos hy,
          rw linear_ordered_comm_group.extend.mul_zero,
          rw if_pos (is_ideal.mul_left _ hy) },
        { have hxy : x * y ∉ S,
          { intro hxy,
            cases is_prime_ideal.mem_or_mem_of_mul_mem hxy with h h,
            { exact hx h },
            { exact hy h } },
          { rw [if_neg hx, if_neg hy, if_neg hxy, mul_one] } } }
    end,
  map_add  := λ x y, begin
      by_cases hxy : x + y ∈ S,
      { rw if_pos hxy, left, trivial },
      { rw if_neg hxy,
        by_cases hx : x ∈ S,
        { have hy : y ∉ S := mt (is_ideal.add hx) hxy,
          right,
          rw if_neg hy },
        { left,
          rw if_neg hx } }
    end }

end trivial

def supp : set R := {x | f x = 0}

instance : is_prime_ideal (supp f) :=
{ zero_ := map_zero f,
  add_  := λ x y hx hy, or.cases_on (map_add f x y)
    (λ hxy, le_antisymm (hx ▸ hxy) trivial)
    (λ hxy, le_antisymm (hy ▸ hxy) trivial),
  smul  := λ c x hx, calc f (c * x)
                        = f c * f x : map_mul f c x
                    ... = f c * 0 : congr_arg _ hx
                    ... = 0 : linear_ordered_comm_group.extend.mul_zero _,
  ne_univ := λ h, have h1 : (1:R) ∈ supp f, by rw h; trivial,
    have h2 : f 1 = 0 := h1,
    by rw [map_one f] at h2; exact option.no_confusion h2,
  mem_or_mem_of_mul_mem := λ x y hxy, begin
      dsimp [supp] at hxy ⊢,
      rw [map_mul f x y] at hxy,
      exact linear_ordered_comm_group.extend.eq_zero_or_eq_zero_of_mul_eq_zero _ _ hxy
    end }

/-
definition extension_to_integral_domain {α : Type} [linear_ordered_comm_group α]
  {R : Type} [comm_ring R] (f : R → option α) [H : is_valuation f] :
  (comm_ring.quotient R (supp f)) → option α := sorry
-/

definition value_group {α : Type*} [linear_ordered_comm_group α]
  {R : Type} [comm_ring R] (f : R → option α) [H : is_valuation f] := 
  group.closure {a : α | ∃ r : R, f r = some a}

instance {α : Type*} [linear_ordered_comm_group α]
  {R : Type*} [comm_ring R] (f : R → option α) [H : is_valuation f] : group (value_group f) :=
  @subtype.group _ _ (value_group f) (group.closure.is_subgroup {a : α | ∃ r : R, f r = some a})



/- Wedhorn 1.27 (ii) -/
-- WR ARE NO LONGER USING AN EQUIV RELN FOR VALUATIONS
/-
instance valuations.setoid (R : Type) [comm_ring R] : setoid (valuations R) :=
{ r := λ v w, ∀ r s : R, v.f r ≤ v.f s ↔ w.f r ≤ w.f s,
  iseqv := ⟨
    -- reflexivity 
    λ _ _ _,iff.rfl,
    -- symmetry
    λ v w H r s,(H r s).symm,
    -- transitivity
    λ v w x Hvw Hwx r s,iff.trans (Hvw r s) (Hwx r s)⟩
} 
-/

/-
theorem equiv_value_group_map (R : Type) [comm_ring R] (v w : valuations R) (H : v ≈ w) :
∃ φ : value_group v.f → value_group w.f, is_group_hom φ ∧ function.bijective φ :=
begin
  existsi _,tactic.swap,
  { intro g,
    cases g with g Hg,
    unfold value_group at Hg,
    unfold group.closure at Hg,
    dsimp at Hg,
    induction Hg,
  },
  {sorry 

  }
end 
-/

end is_valuation


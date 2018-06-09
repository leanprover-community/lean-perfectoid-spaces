import algebra.group_power
--import Kenny_comm_alg.temp
import set_theory.cardinal
import ring_theory.ideals
import for_mathlib.subrel 
import for_mathlib.ideals 

class linear_ordered_comm_group (α : Type)
    extends comm_group α, linear_order α :=
(mul_le_mul_left : ∀ {a b : α}, a ≤ b → ∀ c : α, c * a ≤ c * b)

class linear_ordered_comm_monoid (α : Type)
    extends comm_monoid α, linear_order α :=
(mul_le_mul_left : ∀ {a b : α}, a ≤ b → ∀ c : α, c * a ≤ c * b)

local infix ^ := monoid.pow

namespace linear_ordered_comm_group

variables {α : Type} [linear_ordered_comm_group α] {x y z : α}
variables {β : Type} [linear_ordered_comm_group β]

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

class is_valuation {α : Type} [linear_ordered_comm_group α]
  {R : Type} [comm_ring R] (f : R → option α) : Prop :=
(map_zero : f 0 = 0)
(map_one  : f 1 = 1)
(map_mul  : ∀ x y, f (x * y) = f x * f y)
(map_add  : ∀ x y, f (x + y) ≤ f x ∨ f (x + y) ≤ f y)

namespace is_valuation

variables {α : Type} [linear_ordered_comm_group α]
variables {R : Type} [comm_ring R] (f : R → option α)
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

end is_valuation
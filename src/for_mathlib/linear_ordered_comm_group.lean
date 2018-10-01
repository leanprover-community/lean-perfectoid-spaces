import data.equiv.basic
import group_theory.subgroup
import set_theory.cardinal
import for_mathlib.subrel
import for_mathlib.option_inj

universes u v

class linear_ordered_comm_monoid (α : Type*) extends comm_monoid α, linear_order α :=
(mul_le_mul_left : ∀ {a b : α}, a ≤ b → ∀ c : α, c * a ≤ c * b)

class linear_ordered_comm_group (α : Type*) extends comm_group α, linear_order α :=
(mul_le_mul_left : ∀ {a b : α}, a ≤ b → ∀ c : α, c * a ≤ c * b)

namespace linear_ordered_comm_group

variables {α : Type u} [linear_ordered_comm_group α] {x y z : α}
variables {β : Type v} [linear_ordered_comm_group β]

class is_hom (f : α → β) extends is_group_hom f : Prop :=
(ord : ∀ {a b : α}, a ≤ b → f a ≤ f b)

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
lemma eq_one_of_pow_eq_one {n : ℕ} (H : x ^ (n+1) = 1) : x = 1 :=
begin
  induction n with n ih,
  { simpa using H },
  { cases le_total x 1,
  all_goals { have h1 := mul_le_mul_right h (x ^ (n+1)),
      rw pow_succ at H,
      rw [H, one_mul] at h1 },
    { have h2 := pow_le_one_of_le_one h,
      exact ih (le_antisymm h2 h1) },
    { have h2 := one_le_pow_of_one_le h,
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
  mem_of_between := λ x y hxy hy1 hx, le_antisymm (is_group_hom.one f ▸ is_hom.ord _ hy1) (hx ▸ is_hom.ord _ hxy) }

def height (α : Type) [linear_ordered_comm_group α] : cardinal :=
cardinal.mk {S : set α // is_proper_convex S}

end linear_ordered_comm_group

namespace with_zero

variables {α : Type u} {β : Type v}

instance : has_zero (with_zero α) := ⟨none⟩

@[simp] theorem zero_le [partial_order α] {x : with_zero α} : 0 ≤ x :=
begin
  cases x,
  exact le_refl 0,
  exact le_of_lt (with_bot.bot_lt_some x)
end

@[simp] theorem none_le [partial_order α] {x : with_zero α} :
@has_le.le (with_zero α) _ none x := zero_le

@[simp] theorem not_some_le_zero [partial_order α] {x : α} :
¬ @has_le.le (with_zero α) _ (some x) 0 :=
λ h, option.no_confusion (le_antisymm h zero_le)

@[simp] theorem not_some_le_none [partial_order α] {x : α} :
¬ @has_le.le (with_zero α) _ (some x) none :=
λ h, option.no_confusion (le_antisymm h zero_le)
def map (f : α → β) : with_zero α → with_zero β := option.map f

@[simp] theorem le_zero_iff_eq_zero [partial_order α] {x : with_zero α} : x ≤ 0 ↔ x = 0 :=
by cases x; simp; try {refl}; {intro h, exact option.no_confusion h}

@[simp] lemma map_zero {f : α → β} : map f 0 = 0 := option.map_none'
@[simp] lemma map_none {f : α → β} : map f none = 0 := option.map_none'

@[simp] lemma map_some {f : α → β} {a : α} : map f (some a) = some (f a) := option.map_some'

theorem map_inj {f : α → β} (H : function.injective f) :
function.injective (map f) := option.map_inj H

@[simp] theorem map_le [partial_order α] [partial_order β] {f : α → β}
(H : ∀ a b : α, a ≤ b ↔ f a ≤ f b) :
∀ x y : with_zero α, x ≤ y ↔ map f x ≤ map f y :=
begin
  intros x y,
  cases x; cases y; intros; try {simp},
  { exact H x y }
end

variables [linear_ordered_comm_group α] [linear_ordered_comm_group β]

theorem map_mul (f : α → β) [is_group_hom f] (x y : with_zero α) :
map f (x * y) = option.map f x * option.map f y :=
begin
  cases hx : x; cases hy : y; try {refl},
  show some (f (val * val_1)) = some ((f val) * (f val_1)),
  apply option.some_inj.2,
  exact is_group_hom.mul f val val_1
end 

lemma mul_le_mul_left : ∀ a b : with_zero α, a ≤ b → ∀ c : with_zero α, c * a ≤ c * b
| (some x) (some y) hxy (some z) := begin
    rw with_bot.some_le_some at hxy,
    change @has_le.le (with_zero α) _ (some (z * x)) (some (z * y)),
    simp,
    exact linear_ordered_comm_group.mul_le_mul_left hxy z,
  end
| _        _        hxy 0        := by simp
| (some x) 0        hxy _        := by simp [le_antisymm hxy (le_of_lt (with_bot.bot_lt_some x))]
| 0        _        hxy (some _) := by simp

instance : linear_ordered_comm_monoid (with_zero α) :=
{ mul_le_mul_left := mul_le_mul_left,
  .. with_zero.comm_monoid,
  .. with_zero.linear_order }

theorem eq_zero_or_eq_zero_of_mul_eq_zero : ∀ x y : with_zero α, x * y = 0 → x = 0 ∨ y = 0
| (some x) (some y) hxy := false.elim $ option.no_confusion hxy
| 0        _        hxy := or.inl rfl
| _        0        hxy := or.inr rfl

end with_zero

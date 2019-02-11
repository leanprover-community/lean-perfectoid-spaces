import algebra.group data.option.basic

-- this really shouldn't go here. I blame Chris and Kenny for this nonsense
instance : monad with_zero := option.monad

definition with_zero.inv {Γ : Type*} [has_inv Γ] (x : with_zero Γ) : with_zero Γ :=
do a ← x, return a⁻¹

instance {Γ : Type*} [has_inv Γ] : has_inv (with_zero Γ) := ⟨with_zero.inv⟩

definition with_zero.div {Γ : Type*} [group Γ] (x y : with_zero Γ) : with_zero Γ :=
x * y⁻¹

instance {Γ : Type*} [group Γ] : has_div (with_zero Γ) := ⟨with_zero.div⟩

lemma is_some_iff_ne_none {α : Type*} {x : option α} : x.is_some ↔ x ≠ none :=
by cases x; simp

namespace with_zero
variables {Γ : Type*} [comm_group Γ]

lemma div_eq_div {a b c d : with_zero Γ} (hb : b ≠ 0) (hd : d ≠ 0) :
  a / b = c / d ↔ a * d = b * c :=
begin
  replace hb := is_some_iff_ne_none.2 hb,
  replace hd := is_some_iff_ne_none.2 hd,
  rw option.is_some_iff_exists at hb hd,
  rcases hb with ⟨b, rfl⟩,
  rcases hd with ⟨d, rfl⟩,
  cases a; cases c,
  { refl },
  { change none = some _ ↔ none = some _, simp },
  { change some _ = none ↔ some _ = none, simp },
  change some (_ * _) = some (_ * _) ↔ some (_ * _) = some (_ * _),
  rw [option.some_inj, option.some_inj], split; intro H,
  { rw mul_inv_eq_iff_eq_mul at H,
    rw [H, mul_right_comm, inv_mul_cancel_right, mul_comm] },
  { rw [mul_inv_eq_iff_eq_mul, mul_right_comm, mul_comm c, ← H, mul_inv_cancel_right] }
end

@[simp] lemma zero_ne_some {a : Γ} : (0 : with_zero Γ) ≠ some a :=
λ h, option.no_confusion h

@[simp] lemma some_ne_zero {a : Γ} : (some a : with_zero Γ) ≠ (0 : with_zero Γ) :=
λ h, option.no_confusion h

end with_zero

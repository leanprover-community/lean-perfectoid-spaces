import algebra.group data.option.basic order.basic

-- this really shouldn't go here. I blame Chris and Kenny for this nonsense
instance : monad with_zero := option.monad

namespace with_zero
variables {Γ : Type*}

instance : has_zero (with_zero Γ) := ⟨none⟩

instance [one : has_one Γ] : zero_ne_one_class (with_zero Γ) :=
{ zero_ne_one := λ h, option.no_confusion h,
  .. with_zero.has_zero, .. one }

definition inv [has_inv Γ] (x : with_zero Γ) : with_zero Γ :=
do a ← x, return a⁻¹

instance [has_inv Γ] : has_inv (with_zero Γ) := ⟨with_zero.inv⟩

@[simp] lemma inv_coe [has_inv Γ] (x : Γ) : (x : with_zero Γ)⁻¹ = (x⁻¹ : Γ) := rfl
@[simp] lemma inv_zero [has_inv Γ] : (0 : with_zero Γ)⁻¹ = 0 := rfl

definition with_zero.div [group Γ] (x y : with_zero Γ) : with_zero Γ :=
x * y⁻¹

instance [group Γ] : has_div (with_zero Γ) := ⟨with_zero.div⟩

@[simp] lemma zero_div [group Γ] (x : with_zero Γ) : 0 / x = 0 := rfl
@[simp] lemma div_zero [group Γ] (x : with_zero Γ) : x / 0 = 0 := by change x * _ = _; simp

lemma one_div_eq_inv [group Γ] (x : with_zero Γ) : 1 / x = x⁻¹ :=
begin
  cases x, refl,
  show (_ * _) = _,
  simp
end

@[simp] lemma div_one [group Γ] (x : with_zero Γ) : x / 1 = x :=
begin
  cases x, refl,
  show some (_ * _) = _,
  simp
end

@[simp] lemma mul_right_inv [group Γ] (x : with_zero Γ) (h : x ≠ 0) : x * x⁻¹ = 1 :=
begin
  cases x,
  exfalso, exact h rfl,
  show some (_ * _) = _,
  simpa,
end

@[simp] lemma mul_left_inv [group Γ] (x : with_zero Γ) (h : x ≠ 0) : x⁻¹ * x = 1 :=
begin
  cases x,
  exfalso, exact h rfl,
  show some (_ * _) = _,
  simpa,
end

@[simp] lemma mul_inv_rev [group Γ] (x y : with_zero Γ) : (x * y)⁻¹ = y⁻¹ * x⁻¹ :=
begin
  cases x; cases y; try {refl},
  calc (↑((x * y)⁻¹) : with_zero Γ) = ↑(y⁻¹ * x⁻¹) : by simp [mul_inv_rev]
end

end with_zero

lemma is_some_iff_ne_none {α : Type*} {x : option α} : x.is_some ↔ x ≠ none :=
by cases x; simp

namespace with_zero
variables {Γ : Type*} [comm_group Γ] {a b c d : with_zero Γ}

lemma div_eq_div (hb : b ≠ 0) (hd : d ≠ 0) : a / b = c / d ↔ a * d = b * c :=
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

variable (a)

lemma mul_div_cancel (hb : b ≠ 0) : a * b / b = a :=
begin
  show _ * _ * _ = _,
  simp [mul_assoc, hb],
end

lemma div_mul_cancel (hb : b ≠ 0) : a / b * b = a :=
begin
  show _ * _ * _ = _,
  simp [mul_assoc, hb],
end

variable {a}

lemma div_eq_iff_mul_eq (hb : b ≠ 0) : a / b = c ↔ c * b = a :=
⟨λ h, by rw [← h, div_mul_cancel _ hb],
 λ h, by rw [← h, mul_div_cancel _ hb]⟩

@[simp] lemma zero_ne_some {a : Γ} : (0 : with_zero Γ) ≠ some a :=
λ h, option.no_confusion h

@[simp] lemma some_ne_zero {a : Γ} : (some a : with_zero Γ) ≠ (0 : with_zero Γ) :=
λ h, option.no_confusion h

end with_zero

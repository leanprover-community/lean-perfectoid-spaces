import ring_theory.algebra
import linear_algebra.linear_combination

local attribute [instance, priority 0] classical.prop_decidable
noncomputable theory

namespace lc
open finsupp
variables {R : Type*} {A : Type*} [comm_ring R] [ring A] [algebra R A]
variables (f g h : lc R A)

def one : lc R A := single 1 1

instance : has_one (lc R A) := ⟨one⟩

lemma one_def : (1 : lc R A) = single 1 1 := rfl

def mul := f.sum $ λ r a, g.sum $ λ s b, single (r * s) (a * b)

instance : has_mul (lc R A) := ⟨mul⟩

lemma mul_def :
  f * g = (f.sum $ λ r a, g.sum $ λ s b, single (r * s) (a * b)) := rfl

@[simp] lemma one_mul : 1 * f = f :=
by simp [one_def, mul_def, sum_single_index]

@[simp] lemma mul_one : f * 1 = f :=
by simp [one_def, mul_def, sum_single_index]

lemma mul_assoc : (f * g) * h = f * (g * h) :=
begin
  repeat {rw mul_def},
  rw sum_sum_index,
  { congr' 1,
    funext a r,
    repeat {rw sum_sum_index},
    { congr' 1,
      funext b s,
      rw sum_sum_index,
      { simp only [sum_single_index, zero_mul, sum_zero, single_zero, mul_zero],
        congr' 1,
        funext,
        repeat {rw mul_assoc} },
      all_goals { simp [left_distrib] } },
    swap 4,
    { intros,
      erw ← sum_add,
      simp [right_distrib] },
    all_goals { simp [left_distrib] } },
  { simp },
  { intros,
    erw ← sum_add,
    simp [right_distrib] }
end

instance : monoid (lc R A) :=
{ mul := mul,
  mul_assoc := mul_assoc,
  one_mul := one_mul,
  mul_one := mul_one,
  ..lc.has_one }

lemma left_distrib : f * (g + h) = f * g + f * h :=
by simp only [mul_def, sum_add_index, left_distrib, sum_add, sum_zero, mul_zero,
  single_add, single_zero, eq_self_iff_true, add_right_inj, forall_3_true_iff, forall_true_iff]

lemma right_distrib : (f + g) * h = f * h + g * h :=
by simp only [mul_def, sum_add_index, right_distrib, sum_add, sum_zero, zero_mul,
  single_add, single_zero, eq_self_iff_true, add_right_inj, forall_3_true_iff, forall_true_iff]

instance : ring (lc R A) :=
{ left_distrib := left_distrib,
  right_distrib := right_distrib,
  ..lc.monoid,
  ..lc.add_comm_group }

instance single.is_ring_hom : is_ring_hom (single 1 : R → lc R A) :=
{ map_one := rfl,
  map_mul := λ _ _, by simp [mul_def, sum_single_index],
  map_add := λ _ _, single_add }

instance single_swap.is_monoid_hom :
  is_monoid_hom ((λ r, single (algebra_map A r) 1) : R → lc R A) :=
{ map_one := by simpa,
  map_mul := λ _ _, by simp [mul_def, sum_single_index] }

instance : algebra R (lc R A) :=
{ to_fun := single 1,
  hom := by apply_instance,
  commutes' := by simp [mul_def, sum_single_index, mul_comm],
  smul_def' := λ r f, finsupp.induction f (by simp) $ λ a b f ha hb IH,
    by simp [mul_def, sum_single_index, smul_add, IH, left_distrib] }

instance total.is_ring_hom : is_ring_hom (lc.total R A) :=
{ map_one := by rw [one_def, total_single, one_smul],
  map_mul := λ f g,
  begin
    repeat {erw total_apply},
    rw mul_def,
    rw sum_mul,
    simp only [mul_sum],
    rw sum_sum_index,
    { apply finset.sum_congr rfl,
      intros a ha,
      change finsupp.sum _ _ = sum _ _,
      rw sum_sum_index,
      { apply finset.sum_congr rfl,
        intros b hb,
        change finsupp.sum _ _ = _,
        rw sum_single_index,
        { change _ = _ • _ * _ • _,
          rw [algebra.smul_mul_assoc, algebra.mul_smul_comm, smul_smul] },
        { apply zero_smul } },
      { apply zero_smul },
      { intros, apply add_smul } },
    { apply zero_smul },
    { intros, apply add_smul }
  end,
  map_add := (lc.total R A).map_add }

def atotal : lc R A →ₐ[R] A :=
{ hom := by apply_instance,
  commutes' := λ r, by convert total_single _ _; simp [algebra.smul_def],
  ..lc.total R A }

section
open finset

lemma support_mul (f g : lc R A) :
  (f * g).support ⊆ (image (λ x : A × A, x.fst * x.snd) $ f.support.product g.support) :=
begin
  rw mul_def,
  refine subset.trans support_sum _,
  intros a' ha,
  erw mem_bind at ha,
  rcases ha with ⟨a, ha₁, ha₂⟩,
  have hb := finsupp.support_sum ha₂,
  erw mem_bind at hb,
  rcases hb with ⟨b, hb₁, hb₂⟩,
  have H := finsupp.support_single_subset hb₂,
  erw set.mem_singleton_iff at H,
  subst H,
  rw mem_image,
  use (a, b),
  split,
  { rw mem_product,
    split; assumption },
  { simp * }
end

end

end lc

namespace lc
open finsupp finset
variables {R : Type*} {A : Type*} [comm_ring R] [comm_ring A] [algebra R A]
variables (f g : lc R A)

lemma mul_comm : f * g = g * f :=
begin
  simp only [mul_def, finsupp.sum],
  rw sum_comm,
  iterate 2 {congr' 1, funext},
  congr' 1; rw mul_comm,
end

instance : comm_ring (lc R A) :=
{ mul_comm := mul_comm,
  ..lc.ring }

end lc

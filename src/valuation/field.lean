import for_mathlib.topological_field
import for_mathlib.topology
import for_mathlib.division_ring
--import for_mathlib.uniform_space.uniform_field
import valuation.topology

open filter set

local attribute [instance, priority 0] classical.decidable_linear_order
variables {Γ : Type*} [linear_ordered_comm_group Γ]


def valued_ring (R : Type*) [ring R] (v : valuation R Γ) := R

namespace valued_ring
variables {R : Type*} [ring R]
variables (v : valuation R Γ)

instance : ring (valued_ring R v) := ‹ring R›

instance : ring_with_zero_nhd (valued_ring R v) := valuation.ring_with_zero_nhd v

instance : uniform_space (valued_ring R v) := topological_add_group.to_uniform_space _

instance : uniform_add_group (valued_ring R v) := topological_add_group_is_uniform

variables {K : Type*} [division_ring K] (ν : valuation K Γ)

instance : division_ring (valued_ring K ν) := ‹division_ring K›
end valued_ring

section
variables {K : Type*} [division_ring K] (v : valuation K Γ)

variables x y : units K

-- The following is meant to be the main technical lemma ensuring that inversion is continuous
-- in the topology induced by a valuation on a division ring (ie the next instance)
-- [BouAC, VI.5.1 Lemme 1]
lemma top_div_ring_aux {x y : units K} {γ : Γ} (h : v (x - y) < min (γ * ((v y) * (v y))) (v y)) :
  v (x⁻¹.val - y⁻¹.val) < γ :=
begin
  have hyp1 : v (x - y) < γ * ((v y) * (v y)),
    from lt_of_lt_of_le h (min_le_left _ _),
  have hyp1' : v (x - y) * ((v y) * (v y))⁻¹ < γ,
    from with_zero.mul_inv_lt_of_lt_mul hyp1,
  have hyp2 : v (x - y) < v y,
    from lt_of_lt_of_le h (min_le_right _ _),
  have key : v x = v y, from valuation.map_eq_of_sub_lt v hyp2,
  have decomp : x⁻¹.val - y⁻¹.val = x⁻¹.val * (y.val - x.val) * y⁻¹.val,
  by rw [mul_sub_left_distrib, sub_mul, mul_assoc,
        show y.val * y⁻¹.val = 1, from y.val_inv,
        show x⁻¹.val * x.val = 1, from x.inv_val, mul_one, one_mul],
  calc
    v (x⁻¹.val - y⁻¹.val) = v (x⁻¹.val * (y.val - x.val) * y⁻¹.val) : by rw decomp
    ... = (v x⁻¹.val) * (v $ y.val - x.val) * (v y⁻¹.val) : by repeat { rw valuation.map_mul }
    ... = (v x)⁻¹ * (v $ y.val - x.val) * (v y)⁻¹ : by repeat { rw valuation.map_inv }
    ... = (v $ y.val - x.val) * ((v y) * (v y))⁻¹ : by
      rw [mul_assoc, mul_comm, key, mul_assoc, ← with_zero.mul_inv_rev]
    ... = (v $ y - x) * ((v y) * (v y))⁻¹ : rfl
    ... = (v $ x - y) * ((v y) * (v y))⁻¹ : by rw valuation.map_sub_swap
    ... < γ : hyp1',
end

/-- The topology coming from a valuation on a division rings make it a topological division ring
    [BouAC, VI.5.1 middle of Proposition 1] -/
instance valuation.topological_division_ring : topological_division_ring (valued_ring K v) :=
{ continuous_inv :=
    begin
      let Kv := valued_ring K v,
      have H : units.val ∘ (λ x : units Kv, x⁻¹) = (λ x : Kv, x⁻¹) ∘ units.val,
        by ext ;simp,
      rw continuous_iff_continuous_at,
      intro x,
      let emb := topological_ring.units_embedding Kv,
      apply emb.tendsto_iff emb H,
      unfold continuous_at,
      rw  topological_add_group.tendsto_nhds_nhds_iff (λ (x : Kv), x⁻¹) x.val x.val⁻¹,
      intros V V_in,
      cases (of_subgroups.nhds_zero _).1 V_in with γ Hγ,
      let x' : units K := units.mk (x.val : K) (x.inv : K) x.val_inv x.inv_val,
      use { k : Kv | v k < min (γ* ((v x') * (v x'))) (v x')},
      split,
      { refine (of_subgroups.nhds_zero _).2 _,
        cases valuation.unit_is_some v x' with γ' hγ',
        use min (γ * γ' * γ') γ',
        intro k,
        simp only [hγ'],
        intro h, convert h, ext, convert iff.rfl,
        rw [with_zero.coe_min, mul_assoc], refl },
      { intros y ineq,
        apply Hγ,
        rw mem_set_of_eq,
        -- I sort of lost that y is a unit, but fortunately, it is easy to prove it's not zero
        have : y ≠ 0,
        { intro hy,
          simp [hy] at ineq,
          exact lt_irrefl _ ineq.2 },
        let yu := units.mk' this,
        change v ((yu : Kv) - (x : Kv)) < _ at ineq,
        convert top_div_ring_aux v ineq,
        apply congr_arg,
        congr,
        simp },
    end,
  ..(by apply_instance : topological_ring (valued_ring K v)) }

section
-- until the end of this section, all linearly ordered commutative groups will be endowed with
-- the discrete topology
def discrete_ordered_comm_group : topological_space Γ := ⊤
local attribute [instance] discrete_ordered_comm_group

def ordered_comm_group_is_discrete : discrete_topology Γ := ⟨rfl⟩
local attribute [instance] ordered_comm_group_is_discrete

/-- The valuation map restricted to units of a field endowed with the valuation toplogy is
    continuous if we endow the target with discrete topology.
    [BouAC, VI.5.1 end of Proposition 1] -/
lemma continuous_unit_map :
@continuous _ _ (by apply_instance : topological_space (units $ valued_ring K v) ) _ v.unit_map :=
-- The ugly @ seems to comes from the valued_ring trick
begin
  rw continuous_into_discrete_iff,
  intro γ,
  rw is_open_iff_mem_nhds,
  intros x vx,
  rw [nhds_induced, ← nhds_translation_add_neg x.val, comap_comap_comp],
  use {y | v y < v.unit_map x },
  split,
  { -- Patrick has no idea why Lean needs so much baby-sitting. Patrick is tired
    exact @of_subgroups.mem_nhds_zero K _ Γ _ (λ γ : Γ, {k | v k < γ}) _ _ _ _ _ (v.unit_map x) },
  { intros z hz,
    rw [valuation.coe_unit_map] at hz,
    rw [mem_preimage_eq, mem_singleton_iff] at *,
    rw ← vx,
    exact valuation.unit_map.ext v x z (valuation.map_eq_of_sub_lt v hz),},
end

instance valued_ring.separated : separated (valued_ring K v) :=
begin
  apply topological_add_group.separated_of_zero_sep,
  intros x x_ne,
  have := division_ring,
  use {k | v k < v x},
  have : ∃ γ : Γ, v x = γ, from valuation.unit_is_some v (units.mk' x_ne),
  cases this with γ H,
  split,
  { -- again, this will be an ugly win
    convert @of_subgroups.mem_nhds_zero K _ Γ _ (λ γ : Γ, {k | v k < γ}) _ _ _ _ _ γ,
    rw H, refl },
  { simp [le_refl] }
end
end
end

section top_group_extend
open is_group_hom
variables {G : Type*} [group G] [topological_space G] [topological_group G]
variables {H : Type*} [group H] [topological_space H] [topological_group H]
variables {L : Type*} [group L] [topological_space L] [topological_group L]
[t2_space L]

variables {ι : G → H} [is_group_hom ι] (de : dense_embedding ι)
variables {φ : G → L} [is_group_hom φ]

lemma topological_group.extend_is_group_hom (hφ : continuous φ) (h : continuous (de.extend φ)) :
  is_group_hom (de.extend φ) :=
⟨begin
  let Φ := de.extend φ,
  let P := λ x y : H, Φ (x*y) = Φ x*Φ y,
  have closed : is_closed { q : H × H | P q.1 q.2 } :=
    have c1 : continuous (λ q : H × H, Φ (q.1 * q.2)), from continuous_mul'.comp h,
    have c2 : continuous (λ q : H × H, Φ q.1 * Φ q.2),
      from continuous_mul (continuous_fst.comp h) (continuous_snd.comp h),
  is_closed_eq c1 c2,

  apply is_closed_property2 de closed,
  intros x y,
  dsimp [P, Φ],
  rw ← is_group_hom.map_mul ι,
  repeat { rw dense_embedding.extend_e_eq },
  rw is_group_hom.map_mul φ
end⟩
end top_group_extend

section
variables {R : Type*} [ring R] [topological_space R]

end

section
-- In this section K is commutative
variables {K : Type*} [discrete_field K] (v : valuation K Γ)

-- until the end of this section, all linearly ordered commutative groups will be endowed with
-- the discrete topology
local attribute [instance] discrete_ordered_comm_group ordered_comm_group_is_discrete

instance : comm_ring (valued_ring K v) :=
by unfold valued_ring ; apply_instance

-- Patrick doesn't have any idea why Lean needs help here:
instance valued_ring.coe_is_monoid_hom :
  is_monoid_hom (coe : (valued_ring K v) → ring_completion (valued_ring K v)) :=
begin
  let Kv := valued_ring K v,
  haveI := @is_ring_hom.is_semiring_hom Kv (ring_completion Kv) _ _ coe _,
  exact @is_semiring_hom.is_monoid_hom Kv (ring_completion Kv) _ _ coe _,
end

-- and here. It's probaly paying for the wrapper type valued_ring K v
/- noncomputable instance : topological_space (units $ ring_completion $ valued_ring K v) :=
topological_ring.units_topological_space _
  -/

instance : discrete_field (valued_ring K v) := by unfold valued_ring ; apply_instance


--instance valued_ring.completable : completable_top_field (valued_ring K v) := sorry

instance : topological_group (units $ valued_ring K v) :=
topological_division_ring.units_top_group (valued_ring K v)
--#check completable_top_field.dense_units_map (valued_ring K v)
/- lemma units_completion_dense_embedding :
dense_embedding (units.map (coe : (valued_ring K v) → ring_completion (valued_ring K v))) :=
completable_top_field.dense_units_map
 -/--instance ring_completion.units_top_group : topological_group (units $ ring_completion $ valued_ring K v) :=
--sorry

instance regular_of_discrete {α : Type*} [topological_space α] [discrete_topology α] : regular_space α :=
⟨begin
  intros s a s_closed a_not,
  refine ⟨s, is_open_discrete s, subset.refl s, _⟩,
  rw [← empty_in_sets_eq_bot, mem_inf_sets],
  use {a},
  rw nhds_discrete α,
  simp,
  refine ⟨s, subset.refl s, _ ⟩,
  rintro x ⟨xa, xs⟩,
  rw ← mem_singleton_iff.1 xa at a_not,
  exact a_not xs
end⟩

lemma nhds_of_valuation_lt (x : valued_ring K v) (γ : Γ) :
  {y : K | v (y - x) < γ} ∈ nhds x :=
begin
  rw [← nhds_translation_add_neg x],
  refine ⟨{k | v k < γ}, _ , subset.refl _⟩,
  exact @of_subgroups.mem_nhds_zero K _ Γ _ (λ γ : Γ, {k | v k < γ}) _ _ _ _ _ γ
end

/- lemma continous_unit_extension : continuous ((units_completion_dense_embedding v).extend v.unit_map) :=
begin
  let Kv := valued_ring K v,
  let ι := units.map (coe : (valued_ring K v) → ring_completion (valued_ring K v)),
  let de : dense_embedding ι := units_completion_dense_embedding v,
  -- Patrick hates the three next lines. He is clearly punished for something
  haveI : is_group_hom ι := units.is_group_hom _,
  letI : topological_space (units K) := @topological_ring.units_topological_space Kv _ _,
  haveI : topological_space K := (by apply_instance : topological_space Kv),
  have key : is_open (is_group_hom.ker (v.unit_map : units Kv → Γ)),
  { rw is_open_iff_mem_nhds,
    intros x x_in,
    rw [nhds_induced],
    refine ⟨{y | v (y - x) < v.unit_map x }, nhds_of_valuation_lt v _ _, _⟩,
    intros y vy,
    simp [mem_preimage_eq] at vy,
    rw is_group_hom.mem_ker at *,
    rw ← x_in,
    exact valuation.unit_map.ext v _ _ (valuation.map_eq_of_sub_lt v vy) },
  exact continuous_extend_of_open_kernel de key,
end
 -/--#check (units_completion_dense_embedding v).extend v.unit_map
--#check continuous_extend_of_open_kernel
end

-- Kevin has added the thing he needs

section -- paranoid about this uniform space instance

variables {R : Type*} [comm_ring R]

open valuation

-- ring_with_zero_nhd (valuation_field v) is in valuation/topology.lean

noncomputable def valuation_field.uniform_space (v : valuation R Γ) :
uniform_space (valuation_field v) := topological_add_group.to_uniform_space _

local attribute [instance] valuation_field.uniform_space

def valuation_field.uniform_add_group (v : valuation R Γ) : uniform_add_group (valuation_field v) :=
topological_add_group_is_uniform

local attribute [instance]  valuation_field.uniform_add_group

noncomputable example (v : valuation R Γ) : comm_ring (ring_completion (valuation_field v)) := by apply_instance

def valuation_on_completion {R : Type*} [comm_ring R] (v : valuation R Γ) :
  valuation (ring_completion (valuation.valuation_field v)) (value_group v) := sorry

end -- section

import for_mathlib.topological_field
import for_mathlib.topology
import for_mathlib.division_ring
import for_mathlib.uniform_space.uniform_field
import valuation.topology
import topology.algebra.ordered
import tactic.where

open filter set

local attribute [instance, priority 0] classical.decidable_linear_order
variables {Γ : Type*} [linear_ordered_comm_group Γ]

section with_zero_topology

def with_zero.topological_space : topological_space (with_zero Γ) :=
topological_space.generate_from
({U | ∃ γ : Γ, U = {γ}} ∪ {U | ∃ γ₀ : Γ, U = {γ | γ < γ₀}})

local attribute [instance] with_zero.topological_space

lemma with_zero.is_open_point (γ : Γ) : is_open ({γ} : set $ with_zero Γ) :=
topological_space.generate_open.basic _ (or.inl ⟨γ, rfl⟩)

lemma with_zero.nhds_coe (γ : Γ) : nhds (γ : with_zero Γ) = pure (γ : with_zero Γ) :=
begin
  apply le_antisymm,
  { intros U U_in,
    rw mem_pure_iff at U_in,
    rw mem_nhds_sets_iff,
    exact ⟨({γ} : set $ with_zero Γ),
           ⟨singleton_subset_iff.2 U_in, with_zero.is_open_point γ, mem_singleton _⟩⟩ },
  exact pure_le_nhds _,
end

def with_zero.ordered_topology : ordered_topology (with_zero Γ) :=
{ is_closed_le' :=
  begin
    show is_open {p : with_zero Γ × with_zero Γ | ¬p.fst ≤ p.snd},
    simp only [not_le],
    rw is_open_iff_mem_nhds,
    rintros ⟨a,b⟩ hab,
    change b < a at hab,
    by_cases hb : b = 0,
    { change b = 0 at hb, subst hb,
      have ha := lt_iff_le_and_ne.mp hab,
      cases ha with h₁ h₂,
      replace h₂ := h₂.symm,
      rw with_zero.ne_zero_iff_exists at h₂,
      rcases h₂ with ⟨a, rfl⟩,
      refine mem_sets_of_superset
        (prod_mem_nhds_sets
          (mem_nhds_sets (topological_space.generate_open.basic _ _) (mem_singleton _))
          (mem_nhds_sets (topological_space.generate_open.basic _ _) _)) _,
      work_on_goal 1 { left, exact ⟨a, rfl⟩ },
      work_on_goal 1 { right, exact ⟨a, rfl⟩ },
      work_on_goal 0 { exact hab },
      rintro _ ⟨_, _⟩, simp * at * },
    { refine mem_sets_of_superset
        (prod_mem_nhds_sets
          (mem_nhds_sets _ (mem_singleton _))
          (mem_nhds_sets _ (mem_singleton _))) _,
      { apply topological_space.generate_open.basic,
        left,
        have ha : a ≠ 0,
        { rintro rfl,
          rw lt_iff_le_and_ne at hab,
          cases hab,
          simp * at * },
        rw with_zero.ne_zero_iff_exists at ha,
        rcases ha with ⟨a, rfl⟩,
        exact ⟨_, rfl⟩ },
      { apply topological_space.generate_open.basic,
        left,
        change b ≠ 0 at hb,
        rw with_zero.ne_zero_iff_exists at hb,
        rcases hb with ⟨b, rfl⟩,
        exact ⟨_, rfl⟩ },
      { simp * at * } }
  end }

end with_zero_topology

def valued_ring (R : Type*) [ring R] (v : valuation R Γ) := R

namespace valued_ring
variables {R : Type*} [ring R]
variables (v : valuation R Γ)

local attribute [instance] ring_with_zero_nhd.topological_space
local attribute [instance] ring_with_zero_nhd.is_topological_ring

instance : ring (valued_ring R v) := ‹ring R›

instance : ring_with_zero_nhd (valued_ring R v) := valuation.ring_with_zero_nhd v

instance : uniform_space (valued_ring R v) := topological_add_group.to_uniform_space _

instance : uniform_add_group (valued_ring R v) := topological_add_group_is_uniform

instance : topological_ring (valued_ring R v) := by apply_instance

variables {K : Type*} [division_ring K] (ν : valuation K Γ)

instance : division_ring (valued_ring K ν) := ‹division_ring K›

def valuation : valuation (valued_ring R v) Γ := v

local attribute [instance] with_zero.topological_space with_zero.ordered_topology

local attribute [instance] valuation.subgroups_basis

instance (γ : Γ) : is_add_subgroup {r : valued_ring R v | v r ≤ ↑γ} :=
valuation.le_is_add_subgroup v γ

lemma continuous_valuation : continuous (valued_ring.valuation v) :=
begin
  apply continuous_generated_from _,
  rintros U hU,
  rcases hU with ⟨γ, rfl⟩ | ⟨γ₀, rfl⟩,
  { convert topological_space.is_open_inter _ {r : valued_ring R v | v r ≤ γ}
      {r : valued_ring R v | (γ : with_zero Γ) ≤ v r} _ _,
    {ext, convert @le_antisymm_iff _ _ (v x) γ, simp, refl},
    { apply open_add_subgroup.is_open_of_open_add_subgroup _ _,
      { apply_instance},
      { apply_instance},
      { apply_instance},
      { use {r : valued_ring R v | v r < γ}, split,
        { exact @is_subgroups_basis.is_op _ _ _ _ (λ γ : Γ, {k | v k < γ}) _ _},
        { exact valuation.lt_is_add_subgroup v γ},
        { intro _, exact le_of_lt},
      }
    },
    { suffices : is_closed {r : valued_ring R v | v r < ↑γ},
      { convert this, ext r, simp, refl },
      apply open_add_subgroup.is_closed ⟨{r : valued_ring R v | v r < ↑γ}, _⟩,
      split,
      { exact @is_subgroups_basis.is_op _ _ _ _ (λ γ : Γ, {k | v k < γ}) _ _},
      { exact valuation.lt_is_add_subgroup v γ}
    },
  },
  { rw preimage_set_of_eq,
    delta valued_ring.valuation,
    delta valued_ring,
    exact @is_subgroups_basis.is_op _ _ _ _ (λ γ : Γ, {k | v k < γ}) _ _ }
end

end valued_ring

section
open is_subgroups_basis

local attribute [instance] valuation.subgroups_basis

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
      cases (nhds_zero _ _).1 V_in with γ Hγ,
      let x' : units K := units.mk (x.val : K) (x.inv : K) x.val_inv x.inv_val,
      use { k : Kv | v k < min (γ* ((v x') * (v x'))) (v x')},
      split,
      { refine (nhds_zero _ _).2 _,
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
    exact @mem_nhds_zero _ _  _  _ (λ γ : Γ, {k | v k < γ}) _ _ },
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
    convert @mem_nhds_zero K _ Γ _ (λ γ : Γ, {k | v k < γ}) _ _ ,
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

instance regular_of_discrete {α : Type*} [topological_space α] [discrete_topology α] :
  regular_space α :=
{ t1 := λ x, is_open_discrete _,
  regular :=
  begin
    intros s a s_closed a_not,
    refine ⟨s, is_open_discrete s, subset.refl s, _⟩,
    erw [← empty_in_sets_eq_bot, mem_inf_sets],
    use {a},
    rw nhds_discrete α,
    simp,
    refine ⟨s, subset.refl s, _ ⟩,
    rintro x ⟨xa, xs⟩,
    rw ← mem_singleton_iff.1 xa at a_not,
    exact a_not xs
  end }

open is_subgroups_basis
local attribute [instance] valuation.subgroups_basis

lemma nhds_of_valuation_lt (x : valued_ring K v) (γ : Γ) :
  {y : K | v (y - x) < γ} ∈ nhds x :=
begin
  rw [← nhds_translation_add_neg x],
  refine ⟨{k | v k < γ}, _ , subset.refl _⟩,
  exact @mem_nhds_zero K _ Γ _ (λ γ : Γ, {k | v k < γ}) _ _
end

local notation `hat` K := ring_completion (valued_ring K v)

instance : completable_top_field (valued_ring K v) :=
{ separated := by apply_instance,
  nice :=
  begin
    set Kv := valued_ring K v,
    rintros F hF h0,
    have cau : cauchy (map units.val F),
      from (cauchy_of_iff_map _ _).1 hF,
    rw [cauchy_of_iff_map, filter.map_map, is_subgroups_basis.cauchy_iff],
    rw [cauchy_of_iff_map, is_subgroups_basis.cauchy_iff] at hF,
    replace hF := hF.2,
    refine ⟨map_ne_bot (ne_bot_of_map cau.1), _⟩,
    intro γ,
    have : ∃ (γ₀ : Γ) (M ∈ F), ∀ x : units Kv, x ∈ M → v x.val ≥ γ₀,
    { unfold zero_not_adh at h0,
      rcases (filter.inf_eq_bot_iff _ _).1 h0 with ⟨U, U_in, M, M_in, H⟩,
      rcases mem_comap_sets.1 U_in with ⟨W, W_in, UW⟩,
      cases (is_subgroups_basis.nhds_zero _ _).1 W_in with γ Hγ,
      use [γ, M, M_in],
      intros x xM,
      apply le_of_not_lt _,
      intro hyp,
      have : x ∈ U ∩ M := ⟨UW (Hγ hyp), xM⟩,
      rwa H at this },
    rcases this with ⟨γ₀, M₀, M₀_in, H₀⟩,
    rcases hF (min (γ * γ₀ * γ₀) γ₀) with ⟨M₁, M₁_in, H₁⟩,
    set inv := λ (x : units (valued_ring K v)), x⁻¹,
    let M := units.val '' (inv '' (M₀ ∩ units.val ⁻¹' M₁)),
    have M_in : M ∈ map (units.val ∘ inv) F,
    { rw ← filter.map_map,
      exact image_mem_map (image_mem_map $ inter_mem_sets M₀_in M₁_in) },
    use [M, M_in],
    rintros _ _ ⟨_, ⟨x, ⟨x_in₀, x_in₁⟩, rfl⟩, rfl⟩ ⟨_, ⟨y, ⟨y_in₀, y_in₁⟩, rfl⟩, rfl⟩,
    replace H₁ : v (y.val- x.val) < ↑(min (γ * γ₀ * γ₀) γ₀) := H₁ _ _ x_in₁ y_in₁,
    specialize H₀ x x_in₀,
    have : v (y.val - x.val) < (min (γ * ((v x.val) * (v x.val))) (v x.val)),
    { refine lt_of_lt_of_le H₁ _,
      rw with_zero.coe_min,
      apply min_le_min _ H₀,
      rw mul_assoc,
      rw ← with_zero.mul_coe,
      have : ((γ₀ * γ₀ : Γ) : with_zero Γ) ≤ v (x.val) * v (x.val),
        from calc ↑γ₀ * ↑γ₀ ≤ ↑γ₀ * v x.val :   actual_ordered_comm_monoid.mul_le_mul_left' H₀
                        ... ≤ _ : actual_ordered_comm_monoid.mul_le_mul_right' H₀,
      exact actual_ordered_comm_monoid.mul_le_mul_left' this },
    exact top_div_ring_aux v this
  end }

noncomputable
instance : topological_space (units (ring_completion (valued_ring K v))) :=
topological_ring.units_topological_space _

instance tata : topological_group (units (ring_completion (valued_ring K v))) :=
toto _

local attribute [instance] help_tcs

lemma continuous_unit_extension : continuous ((dense_units_map (valued_ring K v)).extend v.unit_map) :=
begin
  let Kv := valued_ring K v,
  let ι := ring_completion.units_coe (valued_ring K v),
  let de : dense_embedding ι := dense_units_map (valued_ring K v),

  -- Patrick hates the three next lines. He is clearly punished for something
  haveI : is_group_hom ι := units.is_group_hom _,
  letI : topological_space (units Kv) := @topological_ring.units_topological_space Kv _ _,
  haveI : topological_group (units hat K) := topological_division_ring.units_top_group _,
  have key : @is_open (units $ valued_ring K v) _ (is_group_hom.ker (v.unit_map : units (valued_ring K v) → Γ)),
  { rw is_open_iff_mem_nhds,
    intros x x_in,
    rw [nhds_induced],
    refine ⟨{y : Kv | v (y - x.val) < v.unit_map x }, nhds_of_valuation_lt v _ _, _⟩,
    intros y vy,
    simp [mem_preimage_eq] at vy,
    rw is_group_hom.mem_ker at *,
    rw ← x_in,
    exact valuation.unit_map.ext v _ _ (valuation.map_eq_of_sub_lt v vy) },

  exact @continuous_extend_of_open_kernel (units Kv) _ _ _ (units $ hat K) _ _ _
    Γ _ _ _ _ ι _ de (valuation.unit_map v) _ key,
end

noncomputable
def valuation.unit_completion_extend : units (hat K) → Γ :=
(dense_units_map (valued_ring K v)).extend v.unit_map

local notation `hatv` := valuation.unit_completion_extend v

set_option class.instance_max_depth 46

instance : is_group_hom (valuation.unit_map v) := by apply_instance

instance titi : is_monoid_hom (coe : (valued_ring K v) → hat K) := by apply_instance

instance : is_group_hom (ring_completion.units_coe $ valued_ring K v) :=
units.is_group_hom _

instance tutu : topological_group (units $ hat K) := topological_division_ring.units_top_group (hat K)

lemma valuation.unit_completion_extend_mul : ∀ x y : units (hat K),
 hatv (x*y) = hatv x * hatv y :=
begin
  let ι := ring_completion.units_coe (valued_ring K v),
  let de : dense_embedding ι := dense_units_map (valued_ring K v),
  let u := units (hat K),
  letI : topological_monoid u := topological_group.to_topological_monoid _,
  have cl : is_closed {p : u × u | hatv (p.1*p.2) = hatv p.1 * hatv p.2},
  { let ch := continuous_unit_extension v,
    refine @is_closed_eq Γ (u × u) (by apply_instance) (by apply_instance) (by apply_instance)
    begin
      exact t2_space_discrete
    end
    (by apply_instance) _ _
      (continuous_mul'.comp ch)
      (continuous_mul (continuous_fst.comp ch) (continuous_snd.comp ch)) },
  have : ∀ x y : units (valued_ring K v), hatv (ι x * ι y) = (hatv $ ι x)*(hatv $ ι y),
  { intros x y,
    have hx : hatv (ι x) = _:= de.extend_e_eq x,
    have hy : hatv (ι y) = _:= de.extend_e_eq y,
    have hxy : hatv (ι $ x * y) = _:= de.extend_e_eq _,
    rw [hx, hy, ← is_group_hom.map_mul ι x y, hxy, is_group_hom.map_mul (valuation.unit_map v)],
     },
  exact is_closed_property2 de cl this
end

-- vhat is the extension of v to hat K

set_option class.instance_max_depth 80

noncomputable def valuation_on_completion_v (x : hat K) : with_zero Γ :=
  if h : x = 0 then 0 else some (valuation.unit_completion_extend v $ units.mk0 x h)

local notation `vhat` := valuation_on_completion_v v

lemma valuation_on_completion_v_zero : valuation_on_completion_v v 0 = 0 := dif_pos rfl

lemma valuation_on_completion_v_nonzero (x : hat K) (hx : x ≠ 0) :
  valuation_on_completion_v v x = some (valuation.unit_completion_extend v $ units.mk0 x hx)
:= dif_neg hx

lemma vhat_extends_hatv :
  (coe : Γ → with_zero Γ) ∘ hatv = vhat ∘ units.val :=
begin
  funext u,
  show _ = valuation_on_completion_v v ↑u,
  rw valuation_on_completion_v_nonzero v ↑u (units.ne_zero u),
  congr',
  apply units.ext,
  refl,
end

section continuity_of_vhat -- making with_zero.topological_space an instance

local attribute [instance] with_zero.topological_space
open function

lemma filter.comap_pure {α : Type*} {β : Type*} {f : α → β} (h : injective f) (a : α) :
  pure a = comap f (pure $ f a) :=
by rw [← filter.map_pure, comap_map h]

lemma with_zero.comap_coe_nhds (γ : Γ) : nhds γ = comap coe (nhds (γ : with_zero Γ)) :=
begin
  rw [nhds_discrete, filter.comap_pure (λ _ _ h, with_zero.coe_inj.1 h) γ],
  change comap coe (pure (γ : with_zero Γ)) = comap coe (nhds ↑γ),
  rw ← with_zero.nhds_coe γ,
end

lemma continuous_vhat : continuous vhat :=
begin
  rw continuous_iff_continuous_at,
  intro x,
  by_cases h : x = 0,
  {
    sorry
  },
  { let u : units (ring_completion (valued_ring K v)) := units.mk0 x h,
    let c := (coe : Γ → with_zero Γ),
    have comm : c ∘ hatv = vhat ∘ units.val, from vhat_extends_hatv v,
    have H : nhds (hatv u) = comap c (nhds $ c (hatv u)),
      from with_zero.comap_coe_nhds _,
    have H' : map units.val (nhds u) = (nhds x),
    { have : range units.val ∈ nhds (u.val),
      { refine mem_nhds_sets _ ⟨u, rfl⟩,
        rw [range_units_val (hat K), is_open_compl_iff],
        -- Lean needs psychological support
        haveI : t1_space (hat K) := @t2_space.t1_space (hat K) _ (@separated_t2 (hat K) _ _),
        exact is_closed_singleton },
      rw [nhds_induced, map_comap this],
      refl },
    have : map hatv (nhds u) ≤ (nhds $ hatv u) :=  continuous.tendsto (continuous_unit_extension v) u,
    rw [H, ← map_le_iff_le_comap, map_comm comm, H'] at this,
    unfold continuous_at,
    rw valuation_on_completion_v_nonzero v x h,
    exact this,
  }
end
#check nhds_discrete
lemma coe_inj : function.injective (coe : valued_ring K v → hat K) :=
(ring_completion.uniform_embedding_coe _).1

lemma coe_de : dense_embedding (coe : valued_ring K v → hat K) :=
(ring_completion.uniform_embedding_coe _).dense_embedding (ring_completion.dense_coe K)

lemma vhat_extends (r : valued_ring K v) : vhat (↑r) = v r :=
begin
  by_cases h : r = 0,
  { -- zero case
    rw h,
    convert (v.map_zero).symm,
    convert valuation_on_completion_v_zero v,
  },
  { -- nonzero
    have H : (r : hat K) ≠ 0,
    { intro h2, apply h, convert coe_inj v h2,
    },
    convert valuation_on_completion_v_nonzero v r H,
    let u : units (valued_ring K v) := units.mk0 r h,
    let ι := ring_completion.units_coe (valued_ring K v),
    let de : dense_embedding ι := dense_units_map (valued_ring K v),
    change v (u : valued_ring K v)= _,
    rw ←valuation.unit_map_eq,
    congr' 1,
    convert (de.extend_e_eq (units.mk0 r _)).symm,
    apply units.ext, refl,
  }
end

end continuity_of_vhat

-- Kevin pulled this lemma out because it takes forever to compile and takes Lean's
-- deterministic timeout meter right to the edge
lemma valuation_on_completion_extend_add_aux :
  is_closed {p : (hat K) × (hat K) | vhat (p.1 + p.2) ≤ vhat p.1 ∨ vhat (p.1 + p.2) ≤ vhat p.2} :=
begin
  letI := @with_zero.topological_space Γ,
  letI := @with_zero.ordered_topology Γ, -- Γ should be explicit in these functions
  convert @is_closed_union _ {p : (hat K) × (hat K) | vhat (p.1 + p.2) ≤ vhat p.1}
    {p : (hat K) × (hat K) | vhat (p.1 + p.2) ≤ vhat p.2 } _ _ _,
  { exact is_closed_le ((continuous_add').comp (continuous_vhat v)) (continuous_fst.comp (continuous_vhat v)) },
  { apply is_closed_le _ _, apply_instance, apply_instance,
    { apply (continuous_add').comp, exact (continuous_vhat v), apply_instance},
    { apply continuous_snd.comp, exact (continuous_vhat v)},
  }
end
.

lemma valuation_on_completion_extend_add (x y : hat K) :
  vhat (x + y) ≤ vhat x ∨ vhat (x + y) ≤ vhat y :=
begin
  let C := {p : (hat K) × (hat K) | vhat (p.1 + p.2) ≤ vhat p.1 ∨ vhat (p.1 + p.2) ≤ vhat p.2},
  have cl : is_closed C := valuation_on_completion_extend_add_aux v,
  have : ∀ x y : valued_ring K v, ((x : hat K), (y : hat K)) ∈ C,
  { intros x y,
    show vhat (x + y) ≤ vhat x ∨ vhat (x + y) ≤ vhat y,
    convert v.map_add x y,
    { convert vhat_extends v (x + y), exact (is_ring_hom.map_add _).symm},
    { exact vhat_extends v x},
    { convert vhat_extends v (x + y), exact (is_ring_hom.map_add _).symm},
    { exact vhat_extends v y},
  },
  -- why does Lean hate Kevin?
  exact @is_closed_property2 _ _ _ _ _ (λ x y, vhat (x + y) ≤ vhat x ∨ vhat (x + y) ≤ vhat y) (coe_de v) cl this x y,
end

-- horrible units version which we now no longer need
-- lemma valuation.unit_completion_extend_add' : ∀ x y : units (hat K),
--  if h : x.val + y.val = 0 then true else
--    hatv (units.mk0 (x.val + y.val) h) ≤ hatv x ∨ hatv (units.mk0 (x.val + y.val) h) ≤ hatv y :=
-- begin
--   let ι := ring_completion.units_coe (valued_ring K v),
--   let de : dense_embedding ι := dense_units_map (valued_ring K v),
--   let u := units (hat K),
--   letI : topological_monoid u := topological_group.to_topological_monoid _,
--   let C := {p : u × u | if h : p.1.val + p.2.val = 0 then true else
--     hatv (units.mk0 ((p.1 : hat K) + p.2) h) ≤ hatv p.1 ∨
--     hatv (units.mk0 ((p.1 : hat K) + p.2) h) ≤ hatv p.2 },
--   have cl : is_closed C,
--   { sorry},
--   -- see line 429 for mul proof. This is topology.
--   have : ∀ x y : units (valued_ring K v), (ι x, ι y) ∈ C,
--   { intros x y,
--     have hx : hatv (ι x) = _:= de.extend_e_eq x,
--     have hy : hatv (ι y) = _:= de.extend_e_eq y,
--     show dite _ _ _,
--     split_ifs, exact trivial,
--     dsimp [valuation.unit_completion_extend, ι],
--     erw dense_embedding.extend_e_eq de x,
--     erw dense_embedding.extend_e_eq de y,
--     dsimp at h,
--     let h' : ((ι x) : hat K) + (ι y) ≠ 0 := h,
--     erw units.coe_map at h',
--     erw units.coe_map at h',
--     rw ← @is_ring_hom.map_add _ _ _ _ (coe : (valued_ring K v) → hat K)
--       (ring_completion.coe_is_ring_hom _) at h',
--     have add_ne_zero : (x : valued_ring K v) + y ≠ 0,
--     { intro H, rw H at h',
--       rw @is_ring_hom.map_zero _ _ _ _ (coe : (valued_ring K v) → hat K)
--         (ring_completion.coe_is_ring_hom _) at h',
--       apply h',
--       refl },
--     suffices H : dense_embedding.extend de (valuation.unit_map v)
--       (units.mk0
--         (↑(ring_completion.units_coe (valued_ring K v) x) +
--          ↑(ring_completion.units_coe (valued_ring K v) y)) h) =
--         valuation.unit_map v (units.mk0 ((x : valued_ring K v) + (y : valued_ring K v)) add_ne_zero),
--     { rw H,
--       rw ←with_zero.some_le_some,
--       rw ←@with_zero.some_le_some _ _ _ (valuation.unit_map v y),
--       rw valuation.unit_map_eq,
--       rw valuation.unit_map_eq,
--       rw valuation.unit_map_eq,
--       exact v.map_add (x : valued_ring K v) (y : valued_ring K v) },
--     convert de.extend_e_eq _,
--     -- the next line took about an hour to write, and has been much minimised
--     exact units.ext
--       (@is_ring_hom.map_add _ _ _ _ _ (ring_completion.coe_is_ring_hom _) x.val y.val).symm
--   },
--   exact is_closed_property2 de cl this
-- end

-- TODO -- this theorem has too many top spaces instances in its definition
/-
The first three sorries below are meant to be entertainment for Kevin
The map_add sorry should be the same level of difficulty than the map_mul proof
Bourbaki's proof (for the whole thing): the extension is a valuation by continuity
-/
noncomputable
def valuation.completion_extend : valuation (ring_completion $ valued_ring K v) Γ :=
⟨λ x, if h : x = 0 then 0 else some (valuation.unit_completion_extend v $ units.mk0 x h),
{ map_zero := by simp,
  map_one := begin
    -- sorry -- code works but is slow
    let ι := ring_completion.units_coe (valued_ring K v),
    let de : dense_embedding ι := dense_units_map (valued_ring K v),
    suffices : some (valuation.unit_completion_extend v (units.mk0 (1 : hat K) zero_ne_one.symm)) = (1 : Γ),
    by simp [this] ; refl,
    have : units.mk0 (1 : hat K) zero_ne_one.symm = (ι (1 : units $ valued_ring K v)),
      apply units.ext, refl,
    dsimp [valuation.unit_completion_extend],
    rw [this, de.extend_e_eq],
    simp [v.map_one],
    exact v.map_one,
  end,
  map_mul := λ x y,
  begin --sorry -- this proof works fine but is slow
    by_cases hx : x = 0 ; simp [hx],
    by_cases hy : y = 0 ; simp [hy],
    have : x*y ≠ 0,
      exact mul_ne_zero hx hy,
    simp [this],
    have : units.mk0 (x * y) this = (units.mk0 x hx) * (units.mk0 y hy),
    { apply units.ext, refl },
    rw this,
    rw  valuation.unit_completion_extend_mul,
    exact with_zero.mul_coe (valuation.unit_completion_extend v $ units.mk0 x hx)
                            (valuation.unit_completion_extend v $ units.mk0 y hy),
  end,
  map_add := valuation_on_completion_extend_add v }⟩
end
--   begin
--     intros x y,
--     split_ifs,
--       left, simp,
--       left, simp,
--       right, simp,
--       left, simp,
--       exfalso, revert h, subst h_1, subst h_2, simp,
--       right, subst h_1, convert le_refl _, simp,
--       subst h_2, left, simp,
--       rw with_zero.some_le_some,
--       rw with_zero.some_le_some,
--       have H : dite (x + y = 0) _ _ := v.unit_completion_extend_add' (units.mk0 x h_1) (units.mk0 y h_2),
--       rw dif_neg h at H,
--       exact H,
--   end }⟩
-- end

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

--set_option pp.all true
--set_option pp.universes false
set_option class.instance_max_depth 100
--set_option trace.class_instances true
universe u

/-
noncomputable def valuation_on_completion' {R : Type u} [comm_ring R] (v : valuation R Γ) :
  valuation
    (ring_completion
      (valued_ring (valuation.valuation_field v) (valuation_field.canonical_valuation v)))
    (value_group v) :=
valuation.completion_extend (valuation_field.canonical_valuation v)
-/

noncomputable def valuation_on_completion {R : Type u} [comm_ring R] (v : valuation R Γ) :
  valuation
    (ring_completion
      (valuation.valuation_field v))
    (value_group v) :=
valuation.completion_extend (valuation_field.canonical_valuation v)

end -- section

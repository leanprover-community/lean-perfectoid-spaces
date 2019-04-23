/-
The goal of this file is to prove the main part of Proposition 7 of Bourbaki GT III 6.8 :

The completion hat K of a Hausdorff topological field is a field if the image under
the mapping x ↦ x⁻¹ of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at 0 is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does *not* prove this proposition, he refers to the general discussion of extending
function defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

The main discussion revolves aroung the diagram

                 x ↦ x⁻¹
    K ←———— K^x ————————→ K^x ——————⟶ K
    |        |            |          |
    |        |            |          |
    ↓        ↓            ↓          ↓
  hat K ←— hat K* - - → hat K* ——⟶ hat K

Where hat K* := hat K ∖ {0}, which will hopefully become the units of hat K

Of course there is type theory inclusion hell everywhere.

Note that, by definition of a topological field, the unit group, endowed with multiplication
and the topology *induced by inclusion*, is a topological group.

Once the completion becomes a topological field, then we want the map
units.map : units K → units (hat K)
to be a continuous group morphism which is a dense embedding.

All this is very general. The application we have in mind is extension of valuations.
In this application K will be equipped with a valuation and the topology on K will be the
nonarchimedean topology coming from v. Checking that this topology is completable in the sense
of the current file is very easy on paper. But, in valuation/field.lean I can't even state it
without type class search hell. Assuming we can prove that, the remaining work revolves around
the diagram

  units K ———→ Γ
     |       ↗
     |      /
     ↓     /
units (hat K)

but constructing that diagonal arrow is ok if the vertical one is indeed a dense group embedding.
-/

import for_mathlib.uniform_space.ring
import for_mathlib.topological_field
import for_mathlib.division_ring

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

lemma set.mem_compl_singleton_iff {α : Type*} (a x : α) : x ∈ -({a} : set α) ↔ x ≠ a :=
by simp only [set.mem_singleton_iff, set.mem_compl_eq]

def cauchy_of {α : Type*} {β : Type*} [U : uniform_space β] (f : α → β) (F : filter α) :=
@cauchy α (uniform_space.comap f U) F

set_option class.instance_max_depth 100

open set ring_completion filter

local attribute [instance] topological_add_group.to_uniform_space topological_add_group_is_uniform

local notation `𝓝` x:70 := nhds x
local notation `𝓤` := uniformity

variables {K : Type*} [discrete_field K] [topological_space K] [topological_ring K]

/-- Zero is not adherent to F -/
def zero_not_adh (F : filter $ units K) : Prop := comap units.val 𝓝 0 ⊓ F = ⊥

variables (K)

instance : topological_space (units K) := topological_space.induced units.val (by apply_instance)

local notation `hat` K := ring_completion K

def help_tc_search : uniform_space (hat K) := ring_completion.uniform_space K
local attribute [instance] help_tc_search
def help_tc_search' : separated (hat K) := ring_completion.separated K
local attribute [instance] help_tc_search'
def help_tc_search'' : complete_space (hat K) := ring_completion.complete_space K
local attribute [instance] help_tc_search''

def hat_star := {x : hat K // x ≠ 0}

instance : topological_space (hat_star K) := subtype.topological_space

instance [separated K] : zero_ne_one_class (hat K) :=
{ zero_ne_one := assume h, zero_ne_one $ (uniform_embedding_coe K).1 h,
  ..ring_completion.comm_ring K }

variables {K}
lemma hat_units_ne_zero [separated K] (x : units $ hat K) : x.val ≠ 0 :=
assume h, have zero_one : (0 : hat K) = 1 := zero_mul x.inv ▸ (h ▸ x.val_inv), zero_ne_one zero_one
variables (K)

def coe_units [separated K] : units K → hat_star K :=
λ x, ⟨x.val, λ h, units.ne_zero x $ (uniform_embedding_coe K).1 h⟩

@[simp]
lemma mul_coe_units [separated K] (x y : units K) : (coe_units K x).val * (coe_units K y).val = (coe_units K $ x*y).val :=
by { simp only [coe_units], rw ← (ring_completion.coe_is_ring_hom K).map_mul, refl }

@[simp]
lemma coe_units_val [separated K] (x : units K): (coe_units K x).val = (x.val : hat K) := rfl

@[simp]
lemma coe_units_one [separated K] : (coe_units K 1).val = 1 :=
by simpa [coe_units]

/-
--@[simp] -- this breaks a later proof.
lemma units.coe_inv' {α : Type*} [division_ring α] (x : units α) :
  ((x⁻¹ : units α) : α) = x⁻¹ := by simp

lemma for_kevin {α : Type*} [division_ring α] (x : units α) :(x : α)⁻¹ = x.inv :=
(units.coe_inv' _).symm -- why doesn't simp work yet?
-/
lemma for_kevin {α : Type*} [division_ring α] (x : units α) :
  (x : α)⁻¹ = x.inv := sorry

lemma coe_units_comm_square [separated K]: subtype.val ∘ coe_units K = (coe : K → hat K) ∘ units.val :=
by { ext x, simp [coe_units] }

lemma range_units_val : range (units.val : units K → K) = -{0} :=
begin
  ext x,
  rw mem_compl_singleton_iff,
  split,
  { rintro ⟨u, hu⟩ h',
    simpa [hu, h'] using u.val_inv },
  { intro h,
    refine ⟨units.mk0 _ h, _⟩,
    simp [units.mk0] }
end

lemma de_coe_units [separated K] : dense_embedding (coe_units K : units K → hat_star K) :=
let de := uniform_embedding_coe K in
⟨λ ⟨x, x_ne⟩, begin
  have dense := ring_completion.dense_coe K x,
  rw mem_closure_iff_nhds at *,
  intros U U_nhds,
  have : ∃ V ∈ 𝓝 x, (0 : hat K) ∉ V ∧ subtype.val ⁻¹' V ⊆ U,
  { haveI : t1_space (hat K) := t2_space.t1_space, -- Why is this needed?!
    rw [nhds_induced] at U_nhds,
    rcases U_nhds with ⟨W, W_nhds, hW⟩,
    use [W ∩ -{0}, inter_mem_sets W_nhds (compl_singleton_mem_nhds x_ne)],
    split,
    { intro h,
      simpa only [not_true, mem_compl_eq, mem_singleton] using h.2 },
    { intros z hz,
      exact hW hz.1 } }, -- no idea why this line is so slow
  rcases this with ⟨V, V_nhds, zero_V, hVU⟩,
  rcases exists_mem_of_ne_empty (dense V V_nhds) with ⟨y, yV, k, hky⟩,
  have y_ne : y ≠ 0,
  { intro h,
    apply zero_V,
    rwa ← h },
  have : (⟨y, y_ne⟩ : hat_star K) ∈ U ∩ range (coe_units K),
  { split,
  { apply hVU, exact yV },
  { have : k ≠ 0,
    { intro h,
      rw [h] at hky,
      exact y_ne hky.symm },
    use units.mk0 k this,
    rw subtype.ext,
    exact hky, },
     },
  exact ne_empty_of_mem this
end,
begin
  intros x y h,
  rw subtype.ext at h,
  ext,
  exact de.1 h
end ,
begin
  intro x,
  rw [nhds_induced units.val x,
      ← ring_completion.comap_nhds_eq x.val,
      nhds_subtype,
      comap_comap_comp, coe_units_comm_square K, ← comap_comap_comp],
  refl
end⟩

lemma range_units_hat_star [separated K] : range (subtype.val : hat_star K → hat K) = -{0} :=
by { rw subtype.val_range, ext, rw mem_compl_singleton_iff, refl }

section

class completable_top_field : Prop :=
(separated : separated K)
(nice : ∀ F : filter (units K), cauchy_of units.val F → zero_not_adh F →
  cauchy_of units.val (map (λ x, x⁻¹) F))

attribute [instance] completable_top_field.separated

variables [completable_top_field K]

def inv_hat_star : hat_star K → hat K := (de_coe_units K).extend (λ x, ((x⁻¹ : K) : hat K))

@[simp]
lemma inv_hat_star_coe_units [separated K] (x : units K) : inv_hat_star K (coe_units K x) = ((x⁻¹ : K) : hat K) :=
(de_coe_units K).extend_e_eq x

lemma continuous_inv_hat_star : continuous (inv_hat_star K : hat_star K → hat K) :=
begin
  refine (de_coe_units K).continuous_extend _,
  intro x,
  set cu := coe_units K,
  letI : uniform_space (units K) := uniform_space.comap units.val _,
  letI : uniform_space (hat_star K) := uniform_space.comap subtype.val _,
  have ne_bot : comap cu 𝓝 x ≠ ⊥,
    from (de_coe_units K).comap_nhds_neq_bot,
  have cauchy_fact : cauchy_of units.val (comap cu $ 𝓝 x),
  { refine cauchy_comap _ cauchy_nhds ne_bot,

    have : (λ p : hat_star K × hat_star K, (p.1.val, p.2.val)) ∘ (λ p : units K × units K, (cu p.1, cu p.2)) =
    (λ p : K × K, ((p.1 : hat K), (p.2 : hat K))) ∘ (λ p : units K × units K, (p.1, p.2)),
    { ext ; simp [cu, coe_units] ; refl },
    change comap (λ p : units K × units K, (cu p.1, cu p.2)) (comap (λ p : hat_star K × hat_star K, (p.1.val, p.2.val)) (𝓤 (hat K))) ≤ comap (λ p : units K × units K, (p.1.val, p.2.val)) (𝓤 K),
    rw comap_comm this,
    apply filter.comap_mono,
    exact ring_completion.comap_uniformity },
  have zero_not : zero_not_adh (comap cu 𝓝 x),
  { have eq_bot : 𝓝 ↑(0 : K) ⊓ 𝓝 x.val = ⊥,
    { by_contradiction h,
      exact x.property (eq_of_nhds_neq_bot  h).symm},
    unfold zero_not_adh,
    rw [← ring_completion.comap_nhds_eq (0 : K), comap_comm (coe_units_comm_square K).symm,
        nhds_induced, ← comap_inf, ← comap_inf, comap_comap_comp, eq_bot],
    exact comap_bot },
  have := completable_top_field.nice (comap cu 𝓝 x) cauchy_fact zero_not,
  have : cauchy (map units.val $ map (λ (x : units K), x⁻¹) (comap cu 𝓝 x)),
    from cauchy_map uniform_continuous_comap  this,
  cases complete_space.complete (cauchy_map uniform_continuous_coe this) with y hy,
  use y,
  change map ((λ (x : units K), ↑(↑x)⁻¹) : units K → hat K) (comap cu 𝓝 x) ≤ 𝓝 y,
  repeat {rw filter.map_map at hy },
  convert hy,
  ext,
  simp,
end

lemma inv_hat_is_inv : ∀ x : hat_star K, x.val*(inv_hat_star K x) = 1 :=
begin
  have cl : is_closed {x : hat_star K | x.val*(inv_hat_star K x) = 1},
    from is_closed_eq
      (continuous_mul continuous_subtype_val (continuous_inv_hat_star K))
      continuous_const,
  have dense : closure (range (coe_units K)) = univ,
    from eq_univ_of_forall (de_coe_units K).dense,
  apply is_closed_property dense cl,
  intro x,
  rw [inv_hat_star_coe_units, for_kevin, coe_units_val,
      ← (ring_completion.coe_is_ring_hom K).map_mul, x.val_inv,
      (ring_completion.coe_is_ring_hom K).map_one]
end

/-- homeomorphim between non-zero elements of hat K and units of hat K -/
def hat_star_is_units : hat_star K ≃ₜ units (hat K) :=
{ to_fun := λ x, ⟨x.val, (inv_hat_star K x),
      inv_hat_is_inv K x, mul_comm x.val (inv_hat_star K x) ▸ (inv_hat_is_inv K x)⟩ ,
  inv_fun := λ x, ⟨x.val, hat_units_ne_zero x⟩,
  left_inv := λ x, by simp,
  right_inv := λ x, units.ext rfl,
  continuous_to_fun := continuous_induced_rng continuous_induced_dom,
  continuous_inv_fun := continuous_induced_rng continuous_induced_dom }

local notation `ψ` := (hat_star_is_units K).to_equiv.to_fun
local notation `ψ⁻¹` := (hat_star_is_units K).to_equiv.inv_fun

def hat_inv (x : hat K) : hat K := if h : x = 0 then 0 else
inv_hat_star K ⟨x , h⟩

/- lemma invinv : (λ (a : units (hat K)), a⁻¹) = ψ ∘ (inv_hat_star K) ∘ ψ⁻¹ :=
begin
  ext x,
  congr,
  apply mul_eq_one_iff_inv_eq.1,
  apply units.ext,
  exact inv_hat_is_inv K ⟨x.val, hat_units_ne_zero x⟩,
end
 -/
variables (K)

lemma hat_inv_zero : hat_inv _ (0 : hat K) = (0 : hat K) :=
by simp [hat_inv]

instance hat_has_inv : has_inv (hat K) := ⟨hat_inv K⟩

lemma hat_mul_inv : ∀ a : hat K, a ≠ 0 → a * a⁻¹ = 1 :=
sorry

instance : discrete_field (hat K) :=
{ inv := hat_inv K,
  zero_ne_one := assume h, discrete_field.zero_ne_one K ((uniform_embedding_coe K).1 h),
  mul_inv_cancel := hat_mul_inv K,
  inv_mul_cancel := by {intro, rw mul_comm, apply hat_mul_inv },
  inv_zero := hat_inv_zero K,
  has_decidable_eq := by apply_instance,
  ..(by apply_instance : comm_ring (hat K)) }

-- Unfortunately, the above instance loose TC search when it comes to finding a topology on
-- units (hat K)
-- TODO: investigate this issue
--instance help_tcs : topological_space (units $ hat K) := topological_ring.units_topological_space _

instance : topological_division_ring (hat K) :=
{ continuous_inv := sorry,
    /- begin
      rw invinv K,
      exact (hat_star_is_units K).continuous_inv_fun.comp (
        (continuous_inv_hat_star K).comp (hat_star_is_units K).continuous_to_fun)
    end, -/
  ..ring_completion.topological_ring K }
end

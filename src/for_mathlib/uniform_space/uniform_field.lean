/-
The goal of this file is to prove the main part of Proposition 7 of Bourbaki GT III 6.8 :

The completion hat K of a Hausdorff topological field is a field if the image under
the mapping x ↦ x⁻¹ of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at 0 is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does *not* prove this proposition, he refers to the general discussion of extending
function defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

The main discussion revolves around the diagram

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
nonarchimedean topology coming from v.

Note that the separated completion of a non-separated topological field is the zero ring, hence
the separation assumption is needed. Indeed the kernel of the completion map is the closure of
zero which is an ideal. Hence it's either zero (and the field is separated) or the full field,
which implies one is sent to zero and the completion ring is trivial.
-/

import topology.algebra.uniform_ring
import for_mathlib.topological_field
import for_mathlib.data.set.basic
import for_mathlib.filter

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

open filter

set_option class.instance_max_depth 100

open set uniform_space uniform_space.completion filter

local attribute [instance] topological_add_group.to_uniform_space topological_add_group_is_uniform

local notation `𝓝` x:70 := nhds x
local notation `𝓤` := uniformity

variables {K : Type*} [discrete_field K] [topological_space K] [topological_ring K]

variables (K)

local notation `hat` := completion

def help_tc_search : uniform_space (hat K) := completion.uniform_space K
local attribute [instance] help_tc_search
def help_tc_search' : separated (hat K) := completion.separated K
local attribute [instance] help_tc_search'
def help_tc_search'' : complete_space (hat K) := completion.complete_space K
local attribute [instance] help_tc_search''

def help_tc_search''' : t1_space (hat K) := t2_space.t1_space
local attribute [instance] help_tc_search'''

instance [separated K] : nonzero_comm_ring (hat K) :=
{ zero_ne_one := assume h, zero_ne_one $ (uniform_embedding_coe K).inj h,
  ..completion.comm_ring K }

class completable_top_field : Prop :=
(separated : separated K)
(nice : ∀ F : filter K, cauchy F → 𝓝 0 ⊓ F = ⊥ → cauchy (map (λ x, x⁻¹) F))

local attribute [instance] completable_top_field.separated

variables [completable_top_field K] [topological_division_ring K] {K}

/-- extension of inversion to `hat K` -/
def hat_inv : hat K → hat K := dense_inducing_coe.extend (λ x : K, (coe x⁻¹ : hat K))

lemma continuous_hat_inv {x : hat K} (h : x ≠ 0) : continuous_at hat_inv x :=
begin
  haveI : regular_space (hat K) := completion.regular_space K,
  refine dense_inducing_coe.tendsto_extend _,
  apply mem_sets_of_superset (compl_singleton_mem_nhds h),
  intros y y_ne,
  rw mem_compl_singleton_iff at y_ne,
  dsimp,
  apply complete_space.complete,
  change cauchy (map (coe ∘ (λ (x : K), x⁻¹)) (comap coe (𝓝 y))),
  rw ← filter.map_map,
  apply cauchy_map (completion.uniform_continuous_coe K),
  apply completable_top_field.nice,
  { apply cauchy_comap,
    { rw completion.comap_coe_eq_uniformity, exact le_refl _ },
    { exact cauchy_nhds },
    { exact dense_inducing_coe.comap_nhds_neq_bot } },
  { have eq_bot : 𝓝 ↑(0 : K) ⊓ 𝓝 y = ⊥,
    { by_contradiction h,
      exact y_ne (eq_of_nhds_neq_bot  h).symm },
    rw [dense_inducing_coe.nhds_eq_comap (0 : K), ← comap_inf,  eq_bot],
    exact comap_bot },
end

lemma hat_inv_extends {x : K} (h : x ≠ 0) : hat_inv (x : hat K) = coe (x⁻¹ : K) :=
dense_inducing_coe.extend_e_eq _
    ((continuous_coe K).continuous_at.comp (topological_division_ring.continuous_inv x h))

lemma hat_inv_is_inv {x : hat K} (x_ne : x ≠ 0) : x*hat_inv x = 1 :=
begin
  haveI : t1_space (hat K) := t2_space.t1_space,
  let f := λ x : hat K, x*hat_inv x,
  let c := (coe : K → hat K),
  change f x = 1,
  have cont : continuous_at f x,
  { letI : topological_space (hat K × hat K) := prod.topological_space,
    have : continuous_at (λ y : hat K, ((y, hat_inv y) : hat K × hat K)) x,
      from continuous_at.prod_mk continuous_id.continuous_at (continuous_hat_inv x_ne),
    exact (_root_.continuous_mul'.continuous_at.comp this : _) },
  have clo : x ∈ closure (c '' -{0}),
  { have := dense_inducing_coe.dense x,
    rw [← image_univ, show (univ : set K) = {0} ∪ -{0}, from (union_compl_self _).symm, image_union] at this,
    apply mem_closure_union this,
    rw image_singleton,
    exact compl_singleton_mem_nhds x_ne },
  have fxclo : f x ∈ closure (f '' (c '' -{0})) := mem_closure_image cont clo,
  have : f '' (c '' -{0}) ⊆ {1},
  { rw image_image,
    rintros _ ⟨z, z_ne, rfl⟩,
    rw mem_singleton_iff,
    rw mem_compl_singleton_iff at z_ne,
    dsimp [c, f],
    rw hat_inv_extends z_ne,
    norm_cast,
    rw mul_inv_cancel z_ne,
    norm_cast },
  replace fxclo := closure_mono this fxclo,
  rwa [closure_singleton, mem_singleton_iff] at fxclo
end

/-
The value of `hat_inv` at zero is not really specified, although it's probably zero.
Here we explicitly enforce the `inv_zero` axiom.
-/
instance completion.has_inv : has_inv (hat K) := ⟨λ x, if x = 0 then 0 else hat_inv x⟩

@[move_cast]
lemma coe_inv (x : K) : ((x⁻¹ : K) : hat K)= (x : hat K)⁻¹ :=
begin
  by_cases h : x = 0,
  { rw [h, inv_zero],
    dsimp [has_inv.inv],
    norm_cast,
    simp [if_pos] },
  { conv_rhs { dsimp [has_inv.inv] },
    norm_cast,
    rw if_neg,
    { exact (hat_inv_extends h).symm },
    { exact λ H, h (completion.dense_embedding_coe.inj H) } }
end

instance : discrete_field (hat K) :=
{ zero_ne_one := assume h, discrete_field.zero_ne_one K ((uniform_embedding_coe K).inj h),
  mul_inv_cancel := λ x x_ne, by { dsimp [has_inv.inv], simp [if_neg x_ne, hat_inv_is_inv x_ne], },
  inv_mul_cancel := λ x x_ne, by { dsimp [has_inv.inv],
                                   rw [mul_comm, if_neg x_ne, hat_inv_is_inv x_ne] },
  inv_zero := show (0 : hat K)⁻¹ = (0 : hat K), by rw_mod_cast inv_zero,
  has_decidable_eq := by apply_instance,
  ..completion.has_inv,
  ..(by apply_instance : comm_ring (hat K)) }

instance : topological_division_ring (hat K) :=
{ continuous_inv := begin
    intros x x_ne,
    have : {y | y⁻¹ = hat_inv y } ∈ 𝓝 x,
    { have : -{(0 : hat K)} ⊆ {y : hat K | y⁻¹ = hat_inv y },
      { intros y y_ne,
        rw mem_compl_singleton_iff at y_ne,
        dsimp [has_inv.inv],
        rw if_neg y_ne },
      exact mem_sets_of_superset (compl_singleton_mem_nhds x_ne) this },
    rw continuous_at.congr this,
    exact continuous_hat_inv x_ne
  end,
  ..completion.top_ring_compl }

#exit

def cauchy_of {α : Type*} {β : Type*} [U : uniform_space β] (f : α → β) (F : filter α) :=
@cauchy α (uniform_space.comap f U) F

lemma cauchy_of_iff_map {α : Type*} {β : Type*} [U : uniform_space β] (f : α → β) (F : filter α) :
cauchy_of f F ↔ cauchy (map f F):=
begin
  split ; intro h ; cases h with ne_bot H,
  { refine ⟨map_ne_bot ne_bot, _⟩,
    rwa [prod_map_map_eq, map_le_iff_le_comap] },
  { split,
    { exact filter.ne_bot_of_map ne_bot },
    { rwa [prod_map_map_eq, map_le_iff_le_comap] at H } },
end
set_option class.instance_max_depth 100

open set uniform_space uniform_space.completion filter

local attribute [instance] topological_add_group.to_uniform_space topological_add_group_is_uniform

local notation `𝓝` x:70 := nhds x
local notation `𝓤` := uniformity

variables {K : Type*} [discrete_field K] [topological_space K] [topological_ring K]

/-- Zero is not adherent to F -/
def zero_not_adh (F : filter $ units K) : Prop := comap units.val 𝓝 0 ⊓ F = ⊥

variables (K)

local notation `hat` K := completion K

def help_tc_search : uniform_space (hat K) := completion.uniform_space K
local attribute [instance] help_tc_search
def help_tc_search' : separated (hat K) := completion.separated K
local attribute [instance] help_tc_search'
def help_tc_search'' : complete_space (hat K) := completion.complete_space K
local attribute [instance] help_tc_search''

def hat_star := {x : hat K // x ≠ 0}

def ts_hat_star : topological_space (hat_star K) := subtype.topological_space
local attribute [instance] ts_hat_star

instance [separated K] : nonzero_comm_ring (hat K) :=
{ zero_ne_one := assume h, zero_ne_one $ (uniform_embedding_coe K).inj h,
  ..completion.comm_ring K }

variables {K}

lemma hat_units_ne_zero [separated K] (x : units $ hat K) : x.val ≠ 0 :=
units.coe_ne_zero x

variables (K)

def coe_units [separated K] : units K → hat_star K :=
λ x, ⟨x.val, λ h, units.ne_zero x $ (uniform_embedding_coe K).inj h⟩

@[simp]
lemma mul_coe_units [separated K] (x y : units K) :
  (coe_units K x).val * (coe_units K y).val = (coe_units K $ x*y).val :=
by { simp only [coe_units], rw ← completion.is_ring_hom_coe.map_mul, refl }

@[simp]
lemma coe_units_val [separated K] (x : units K): (coe_units K x).val = (x.val : hat K) := rfl

@[simp]
lemma coe_units_one [separated K] : (coe_units K 1).val = 1 :=
by simpa [coe_units]

lemma coe_units_comm_square [separated K]: subtype.val ∘ coe_units K = (coe : K → hat K) ∘ units.val :=
by { ext x, simp [coe_units] }


local attribute [instance] topological_ring.topological_space_units

lemma di_coe_units [separated K] : dense_inducing (coe_units K : units K → hat_star K) :=
let de := uniform_embedding_coe K in
{ induced := begin
    rw induced_iff_nhds_eq,
    intro x,
    rw [nhds_induced units.val x, dense_inducing_coe.nhds_eq_comap  x.val, nhds_subtype,
        filter.comap_comm (coe_units_comm_square K : _)],
    refl
  end,
  dense := λ ⟨x, x_ne⟩, begin
    have dense := (dense_range_iff_closure_eq _).mpr completion.dense x,
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
        existsi (units.mk0 k this), -- `use` works but is much slower for some reason
        rw subtype.ext,
        exact hky },
    },
    exact ne_empty_of_mem this
  end }

lemma de_coe_units [separated K] : dense_embedding (coe_units K : units K → hat_star K) :=
{ inj := begin
    intros x y h,
    rw subtype.ext at h,
    ext,
    exact (uniform_embedding_coe K).inj h
  end,
  ..di_coe_units K }

/- lemma range_units_hat_star [separated K] : range (subtype.val : hat_star K → hat K) = -{0} :=
by { rw subtype.val_range, ext, rw mem_compl_singleton_iff, refl } -/

section

class completable_top_field : Prop :=
(separated : separated K)
(nice : ∀ F : filter (units K), cauchy_of units.val F → zero_not_adh F →
  cauchy_of units.val (map (λ x, x⁻¹) F))

local attribute [instance] completable_top_field.separated

variables [completable_top_field K] [topological_division_ring K]

variables {K}

def inv_hat_star_hat : hat_star K → hat K := (di_coe_units K).extend (λ x, ((x⁻¹ : K) : hat K))

@[simp]
lemma inv_hat_star_coe_units [separated K] (x : units K) :
  inv_hat_star_hat (coe_units K x) = ((x⁻¹ : K) : hat K) :=
(di_coe_units K).extend_e_eq x
  ((uniform_continuous_coe K).continuous.continuous_at.comp
    $ by exact_mod_cast (topological_division_ring.continuous_units_inv K).continuous_at)

lemma continuous_inv_hat_star_hat : continuous (inv_hat_star_hat : hat_star K → hat K) :=
begin
  haveI : regular_space (hat K) := separated_regular, -- not clear why this is needed
  refine (di_coe_units K).continuous_extend _,
  intro x,
  set cu := coe_units K,
  letI : uniform_space (units K) := uniform_space.comap units.val _,
  letI : uniform_space (hat_star K) := uniform_space.comap subtype.val _,
  have ne_bot : comap cu 𝓝 x ≠ ⊥,
    from (di_coe_units K).comap_nhds_neq_bot,
  have cauchy_fact : cauchy_of units.val (comap cu $ 𝓝 x),
  { refine cauchy_comap _ cauchy_nhds ne_bot,
    have : (λ p : hat_star K × hat_star K, (p.1.val, p.2.val)) ∘ (λ p : units K × units K, (cu p.1, cu p.2)) =
    (λ p : K × K, ((p.1 : hat K), (p.2 : hat K))) ∘ (λ p : units K × units K, (p.1, p.2)),
    { ext ; simp [cu, coe_units] ; refl },
    change comap (λ p : units K × units K, (cu p.1, cu p.2)) (comap (λ p : hat_star K × hat_star K, (p.1.val, p.2.val)) (𝓤 (hat K))) ≤ comap (λ p : units K × units K, (p.1.val, p.2.val)) (𝓤 K),
    rw comap_comm this,
    apply filter.comap_mono,
    rw completion.comap_coe_eq_uniformity K,
    exact le_refl _ },
  have zero_not : zero_not_adh (comap cu 𝓝 x),
  { have eq_bot : 𝓝 ↑(0 : K) ⊓ 𝓝 x.val = ⊥,
    { by_contradiction h,
      exact x.property (eq_of_nhds_neq_bot  h).symm},
    unfold zero_not_adh,
    rw [(completion.uniform_inducing_coe K).inducing.nhds_eq_comap (0 : K),
        comap_comm (coe_units_comm_square K).symm,
        nhds_induced, ← comap_inf, ← comap_inf, filter.comap_comap_comp, eq_bot],
    exact comap_bot },
  have := completable_top_field.nice (comap cu 𝓝 x) cauchy_fact zero_not,
  have : cauchy (map units.val $ map (λ (x : units K), x⁻¹) (comap cu 𝓝 x)),
    from cauchy_map uniform_continuous_comap  this,
  cases complete_space.complete (cauchy_map (uniform_continuous_coe K) this) with y hy,
  use y,
  change map ((λ (x : units K), ↑(↑x)⁻¹) : units K → hat K) (comap cu 𝓝 x) ≤ 𝓝 y,
  repeat {rw filter.map_map at hy },
  convert hy,
  ext,
  simpa using units.inv_eq_inv x_1
end

lemma inv_hat_is_inv : ∀ x : hat_star K, x.val*(inv_hat_star_hat x) = 1 :=
begin
  have cl : is_closed {x : hat_star K | x.val*(inv_hat_star_hat x) = 1},
    from is_closed_eq
      (_root_.continuous_mul continuous_subtype_val continuous_inv_hat_star_hat)
      continuous_const,
  have dense : closure (range (coe_units K)) = univ,
    from eq_univ_of_forall (de_coe_units K).dense,
  apply is_closed_property dense cl,
  intro x,
  rw [inv_hat_star_coe_units, division_ring.inv_val_eq_inv, coe_units_val,
      ← completion.is_ring_hom_coe.map_mul, x.val_inv,
      completion.is_ring_hom_coe.map_one]
end

lemma inv_hat_ne_zero (x : hat_star K) : inv_hat_star_hat x ≠ 0 :=
λ h,
begin
  have := inv_hat_is_inv x,
  rw [h, mul_zero] at this,
  exact zero_ne_one this,
end

def inv_hat_star : hat_star K → hat_star K :=
λ x, ⟨inv_hat_star_hat x, inv_hat_ne_zero x⟩

lemma continuous_inv_hat_star : continuous (inv_hat_star : hat_star K → hat_star K) :=
continuous_induced_rng continuous_inv_hat_star_hat

/-- homeomorphim between non-zero elements of hat K and units of hat K -/
def hat_star_is_units : hat_star K ≃ₜ units (hat K) :=
{ to_fun := λ x, ⟨x.val, (inv_hat_star_hat x),
      inv_hat_is_inv x, mul_comm x.val (inv_hat_star_hat x) ▸ (inv_hat_is_inv x)⟩ ,
  inv_fun := λ x, ⟨x.val, hat_units_ne_zero x⟩,
  left_inv := λ x, by simp,
  right_inv := λ x, units.ext rfl,
  continuous_to_fun := continuous_induced_rng continuous_induced_dom,
  continuous_inv_fun := continuous_induced_rng continuous_induced_dom }

local notation `ψ` := hat_star_is_units.to_equiv.to_fun
local notation `ψ⁻¹` := hat_star_is_units.to_equiv.inv_fun

def hat_inv (x : hat K) : hat K := if h : x = 0 then 0 else
inv_hat_star_hat ⟨x , h⟩

/- lemma invinv : (λ (a : units (hat K)), a⁻¹) = ψ ∘ inv_hat_star ∘ ψ⁻¹ :=
begin
  ext x,
  congr,
  apply mul_eq_one_iff_inv_eq.1,
  apply units.ext,
  exact inv_hat_is_inv K ⟨x.val, hat_units_ne_zero x⟩,
end
 -/

lemma hat_inv_zero : hat_inv (0 : hat K) = (0 : hat K) :=
by simp [hat_inv]

lemma hat_inv_nonzero (x : hat_star K) : hat_inv x.val = inv_hat_star_hat x :=
by simp [hat_inv, dif_neg x.property]

lemma inv_comm : @inv_hat_star_hat K _ _ _ _ _ = hat_inv ∘ subtype.val :=
by { ext x, exact (hat_inv_nonzero x).symm }

instance hat_has_inv : has_inv (hat K) := ⟨hat_inv⟩

lemma hat_mul_inv : ∀ a : hat K, a ≠ 0 → a * a⁻¹ = 1 :=
begin
  intros a a_ne,
  change a * (hat_inv a) = 1,
  simp [if_neg, a_ne, hat_inv, inv_hat_is_inv ⟨a, a_ne⟩]
end

variables (K)

instance : discrete_field (hat K) :=
{ inv := hat_inv,
  zero_ne_one := assume h, discrete_field.zero_ne_one K ((uniform_embedding_coe K).inj h),
  mul_inv_cancel := hat_mul_inv,
  inv_mul_cancel := by {intro, rw mul_comm, apply hat_mul_inv },
  inv_zero := hat_inv_zero,
  has_decidable_eq := by apply_instance,
  ..(by apply_instance : comm_ring (hat K)) }

-- Unfortunately, the above instance loose TC search when it comes to finding a topology on
-- units (hat K)
-- TODO: investigate this issue
def help_tcs : topological_space (units $ hat K) := topological_ring.topological_space_units _
local attribute [instance] help_tcs

instance : topological_division_ring (hat K) :=
{ continuous_inv := begin
    intros x x_ne,
    let x_star : hat_star K := ⟨x, x_ne⟩,
    let j : hat_star K → hat K := subtype.val,
    have op : (-{0} : set $ hat K) ∈ 𝓝 x,
    { apply mem_nhds_sets,
      rw is_open_compl_iff,
      haveI : t1_space (hat K) := t2_space.t1_space, -- same mystery as above
      exact is_closed_singleton,
      rwa mem_compl_singleton_iff },
    have key : map j (comap j 𝓝 x) = 𝓝 x,
      from map_comap_of_surjective' op (λ y y_ne, ⟨⟨y, mem_compl_singleton_iff.mp y_ne⟩, rfl⟩),
    have : map inv_hat_star_hat (𝓝 x_star) ≤ 𝓝 (inv_hat_star_hat x_star),
      from continuous_inv_hat_star_hat.continuous_at,
    rwa [nhds_induced, ← hat_inv_nonzero, inv_comm, ← filter.map_map, key] at this,
  end,
  ..completion.top_ring_compl }

def completion.coe_is_monoid_hom : is_monoid_hom (coe : K → hat K) :=
{ ..(by apply_instance : is_ring_hom (coe : K → hat K))}

local attribute [instance] completion.coe_is_monoid_hom

def completion.units_coe := (units.map (coe : K → hat K) : units K → units (hat K))
open completion

lemma dense_units_map : dense_embedding (units_coe K : units K → units (hat K)) :=
begin
  rw show units_coe K = ψ ∘ coe_units K,
  { funext,
    apply units.ext,
    refl },
  exact dense_embedding.comp (dense_embedding.of_homeo $ hat_star_is_units) (de_coe_units _),
end
end

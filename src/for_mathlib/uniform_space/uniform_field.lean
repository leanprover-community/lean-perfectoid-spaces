/-
The goal of this file is to prove the main part of Proposition 7 of Bourbaki GT III 6.8 :

The completion hat K of a Hausdorff topological field is a field if the image under
the mapping x ↦ x⁻¹ of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at 0 is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does *not* prove this proposition, he refers to the general discussion of extending
function defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

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

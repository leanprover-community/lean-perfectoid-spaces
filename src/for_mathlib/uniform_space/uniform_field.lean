/-
The goal of this file is to prove, modulo continuous_extend_of_really_wants_to, part of
Proposition 7 of Bourbaki GT III 6.8 :

The completion hat K of a Hausdorff topological field is a field if the image under
the mapping x ↦ x⁻¹ of every Cauchy filter (with respect to the additive uniform structure)
which does not have a cluster point at 0 is a Cauchy filter
(with respect to the additive uniform structure).

Bourbaki does *not* prove this proposition, he refers to the general discussion of extending
function defined on a dense subset with values in a complete Hausdorff space. In particular
the subtlety about clustering at zero is totally left to readers.

In this file I tried a proof distinguishing between the case where K is discrete, hence complete
hence the statement is obvious, and the case where it's not.

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
import for_mathlib.uniform_space.uniform_embedding

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

lemma set.mem_compl_singleton_iff {α : Type*} (a x : α) : x ∈ -({a} : set α) ↔ x ≠ a :=
by simp only [set.mem_singleton_iff, set.mem_compl_eq]

set_option class.instance_max_depth 200

open set ring_completion filter

local attribute [instance] topological_add_group.to_uniform_space topological_add_group_is_uniform

local notation `𝓝` x:70 := nhds x

variables {K : Type*} [discrete_field K] [topological_space K] [topological_ring K]

/-- Zero is not adherent to F -/
def zero_not_adh (F : filter $ units K) : Prop := comap units.val 𝓝 0 ⊓ F = ⊥

variables (K)

instance : topological_space (units K) := topological_space.induced units.val (by apply_instance)

local notation `hat` K := ring_completion K

def help_tc_search : uniform_space (hat K) := ring_completion.uniform_space K
local attribute [instance] help_tc_search

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
lemma coe_units_one [separated K] : (coe_units K 1).val = 1 :=
by simpa [coe_units]

class non_discrete_group (G : Type*) [add_group G] [topological_space G] :=
(zero_not_open : ¬ is_open ({0} : set G))

namespace non_discrete_group
open function
variables (G : Type*) [add_group G] [topological_space G] [non_discrete_group G]
lemma zero_not_mem_nhds : ({0} : set G) ∉ nhds (0 : G) :=
begin
  intro h,
  rcases mem_nhds_sets_iff.1 h with ⟨U, U_sub, U_op, z_in⟩,
  have : U = {0},
    from subset.antisymm U_sub (singleton_subset_iff.2 z_in),
  rw this at U_op,
  exact zero_not_open _ U_op,
end

-- TODO write an efficient proof instead of being upset about trivialities
lemma dense_compl_zero : ∀ (x : G), x ∈ closure (-({0} : set G)) :=
begin
  intro x,
  by_cases h : x = 0,
  { rw [h, mem_closure_iff_nhds],
    rintros U U_in,
    have : U ≠ {0},
      from λ H, non_discrete_group.zero_not_mem_nhds G (H ▸ U_in),
    intro H,
    apply this,
    ext y,
    split ; intro hy,
    { by_contradiction h',
      have : y ∈ U ∩ -{0}, from ⟨hy, h'⟩,
      rwa H at this },
    { rw mem_singleton_iff at hy,
      rw hy,
      rcases mem_nhds_sets_iff.1 U_in with ⟨_, H, _, H'⟩,
      exact H H' } },
  { have : x ∈ -({0} : set G),
    { rw mem_compl_singleton_iff,
      exact h },
    exact subset_closure this },
end

attribute [to_additive is_add_group_hom.trivial_ker_of_inj] is_group_hom.trivial_ker_of_inj

variables {G} {H : Type*} [add_group H] [topological_space H]
lemma of_non_discrete_inj_hom {f : G → H} [is_add_group_hom f] (inj : injective f)
  (cont : continuous f) : non_discrete_group H :=
⟨assume H,
  have k : f ⁻¹' {0} = {0}, from is_add_group_hom.trivial_ker_of_inj f inj,
  zero_not_open G (k ▸ (cont _ H))⟩
end non_discrete_group

instance ring_completion.non_discrete [separated K] [non_discrete_group K]: non_discrete_group (hat K) :=
have ue : uniform_embedding coe, from uniform_embedding_coe K,
non_discrete_group.of_non_discrete_inj_hom ue.1 ue.uniform_continuous.continuous

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

lemma de_units_val [non_discrete_group K] : dense_embedding (units.val : units K → K) :=
begin
  constructor,
  { rw range_units_val K,
    apply non_discrete_group.dense_compl_zero },
  { intros x y h,
    ext,
    exact h },
  { intros a, rw nhds_induced },
end

lemma de_hat_star [separated K] [non_discrete_group K]: dense_embedding (subtype.val : hat_star K → hat K) :=
begin
  constructor,
  { rw subtype.val_range,
    intro x,
    convert non_discrete_group.dense_compl_zero (hat K) x,
    ext,
    rw mem_compl_singleton_iff,
    refl },
  { intros x y h,
    exact subtype.ext.2 h },
  { intros a, rw nhds_induced },
end

lemma de_coe_units [separated K] [non_discrete_group K]: dense_embedding (coe_units K : units K → hat_star K) :=
begin
  have ue : uniform_embedding coe, from uniform_embedding_coe K,
  have := ue.dense_embedding (ring_completion.dense_coe K),
  apply dense_embedding.of_comm_square (de_units_val K) this (de_hat_star K),
  ext, simp [coe_units]
end


lemma range_units_hat_star [separated K] : range (subtype.val : hat_star K → hat K) = -{0} :=
by { rw subtype.val_range, ext, rw mem_compl_singleton_iff, refl }

section

class completable_non_discrete_top_field : Prop :=
(separated : separated K)
(nice : ∀ F : filter (units K), cauchy_of units.val F → zero_not_adh F →
  cauchy_of units.val (map (λ x, x⁻¹) F) ∧ zero_not_adh (map (λ x, x⁻¹) F))

attribute [instance] completable_non_discrete_top_field.separated
variables [non_discrete_group K]

def inv_hat_star [separated K] : hat_star K → hat_star K := (de_coe_units K).extend $ coe_units K ∘ (λ x, x⁻¹)

@[simp]
lemma inv_hat_star_coe_units [separated K] (x : units K) : inv_hat_star K (coe_units K x) = coe_units K x⁻¹ :=
(de_coe_units K).extend_e_eq x


variables [completable_non_discrete_top_field K]

lemma continuous_inv_hat_star : continuous (inv_hat_star K) :=
begin
  let dkX := de_coe_units K, -- dense embedding K* → hat K*
  let diX := de_units_val K, -- dense embedding K* → K
  let ue := uniform_embedding_coe K, -- uniform embedding K → hat K
  let diY := de_hat_star K, -- dense embedding hat K* → hat K

  have comm : subtype.val ∘ coe_units K = coe ∘ units.val, by { ext, refl },
  apply continuous_extend_of_really_wants_to (λ x : units K, x⁻¹) comm comm
    diX dkX diY diX dkX diY ue ue,
  { rw [range_units_val K, range_units_hat_star K, preimage_compl, compl_subset_compl,
       singleton_subset_iff], simp, refl },
  { rw [range_units_val K, range_units_hat_star K, compl_compl, compl_compl,
        singleton_subset_iff],
    use 0,
    simp,
    refl },
  { intros F cauchyF hF,
    have zero_non_unit : (0 : K) ∉ range (units.val : units K → K),
    { rw range_units_val K, simp },
    have non_unit_zero : ∀ (x : K), x ∉ set.range (units.val : units K → K) → x = 0,
    { rw range_units_val K, simp },
    cases completable_non_discrete_top_field.nice F cauchyF (hF (0 : K) zero_non_unit) with h₁ h₂,
    refine ⟨h₁, _⟩,
    intros x hx,
    rwa non_unit_zero x hx },
end

lemma inv_hat_is_inv : ∀ x : hat_star K, x.val*(inv_hat_star K x).val = 1 :=
begin
  have cl : is_closed {x : hat_star K | x.val*(inv_hat_star K x).val = 1},
    from is_closed_eq
      (continuous_mul continuous_subtype_val ((continuous_inv_hat_star K).comp continuous_subtype_val))
      continuous_const,
  have dense : closure (range (coe_units K)) = univ,
    from eq_univ_of_forall (de_coe_units K).dense,
  simp [is_closed_property dense cl]
end

/-- homeomorphim between non-zero elements of hat K and units of hat K -/
def hat_star_is_units : hat_star K ≃ₜ units (hat K) :=
{ to_fun := λ x, ⟨x.val, (inv_hat_star K x).val,
      inv_hat_is_inv K x, mul_comm x.val (inv_hat_star K x).val ▸ (inv_hat_is_inv K x)⟩ ,
  inv_fun := λ x, ⟨x.val, hat_units_ne_zero x⟩,
  left_inv := λ x, by simp,
  right_inv := λ x, units.ext rfl,
  continuous_to_fun := continuous_induced_rng continuous_induced_dom,
  continuous_inv_fun := continuous_induced_rng continuous_induced_dom }

local notation `ψ` := (hat_star_is_units K).to_equiv.to_fun
local notation `ψ⁻¹` := (hat_star_is_units K).to_equiv.inv_fun

def hat_inv (x : hat K) : hat K := if h : x = 0 then 0 else
subtype.val (inv_hat_star K ⟨x , h⟩)

lemma invinv : (λ (a : units (hat K)), a⁻¹) = ψ ∘ (inv_hat_star K) ∘ ψ⁻¹ :=
begin
  ext x,
  congr,
  apply mul_eq_one_iff_inv_eq.1,
  apply units.ext,
  exact inv_hat_is_inv K ⟨x.val, hat_units_ne_zero x⟩,
end

variables (K)

lemma hat_inv_zero : hat_inv _ (0 : hat K) = (0 : hat K) :=
by simp [hat_inv]

instance hat_has_inv : has_inv (hat K) := ⟨hat_inv K⟩

lemma hat_mul_inv : ∀ a : hat K, a ≠ 0 → a * a⁻¹ = 1 :=
begin
  intros a a_ne,
  change a*(hat_inv K a) = 1,
  simp [hat_inv, a_ne, inv_hat_is_inv K ⟨a, a_ne⟩]
end

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
instance help_tcs : topological_space (units $ hat K) := topological_ring.units_topological_space _

instance : topological_division_ring (hat K) :=
{ continuous_inv :=
    begin
      rw invinv K,
      exact (hat_star_is_units K).continuous_inv_fun.comp (
        (continuous_inv_hat_star K).comp (hat_star_is_units K).continuous_to_fun)
    end,
  ..ring_completion.topological_ring K }
end

/-- A topological field is completable if it is either discrete (in the topological sense)
    or if satisfies the completable_non_discrete_top_field condition -/
class completable_top_field (F : Type*) [discrete_field F] [t : topological_space F] [topological_division_ring F]:=
(completable := t = ⊤ ∨ completable_non_discrete_top_field F)

namespace completable_top_field
variables (F : Type*) [discrete_field F] [topological_space F] [topological_division_ring F]
 [completable_top_field F]

instance coe_is_ring_hom  := ring_completion.coe_is_ring_hom K

instance : division_ring (hat F) := sorry

instance : topological_division_ring (hat F) := sorry

instance come_on_lean : is_monoid_hom (coe : F → hat F) :=
{ map_one := sorry,
  map_mul := sorry }

--#check units (hat K)
--#check is_ring_hom
--#check (completable_top_field.coe_is_ring_hom K)
--#check @units.map K (hat K) _ _ (coe : K → hat K) (completable_top_field.come_on_lean K)

lemma dense_units_map :
  dense_embedding (units.map (coe : F → hat F) : units F → units (hat F)) :=
begin
  sorry
end

end completable_top_field

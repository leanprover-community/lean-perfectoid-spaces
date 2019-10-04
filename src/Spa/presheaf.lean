import ring_theory.localization
import ring_theory.subring

import for_mathlib.nonarchimedean.basic
import for_mathlib.topological_rings -- subring of a top ring

import sheaves.presheaf_of_topological_rings
import Spa.rational_open_data

universes u₁ u₂ u₃

open_locale classical

open set function Spv valuation

local postfix `⁺` : 66 := λ A : Huber_pair, A.plus

namespace spa

variable {A : Huber_pair}

section
open topological_space

/-- The set of all rational open subsets contained in the open set U. -/
def rational_open_data_subsets (U : opens (spa A)) :=
{ r : rational_open_data A // r.open_set ⊆ U}

/-- The natural inclusion map of rational open subsets contained in the open set U
into those contained in some larger open set V (that contains U).-/
def rational_open_data_subsets.map {U V : opens (spa A)} (hUV : U ≤ V)
  (rd : rational_open_data_subsets U) :
  rational_open_data_subsets V :=
⟨rd.val, set.subset.trans rd.property hUV⟩

/--The intersection of two rational open subsets contained in some open set U
is a rational open subset contained in U.-/
noncomputable def rational_open_data_subsets_inter {U :  opens (spa A)}
  (r1 r2 : rational_open_data_subsets U) :
rational_open_data_subsets U :=
⟨rational_open_data.inter r1.1 r2.1, begin
  rw rational_open_data.inter_open_set,
  refine set.subset.trans (inter_subset_left r1.1.open_set r2.1.open_set) _,
  exact r1.2
end⟩

lemma rational_open_data_subsets_symm {U :  opens (spa A)}
  (r1 r2 : rational_open_data_subsets U) :
rational_open_data_subsets_inter r1 r2 = rational_open_data_subsets_inter r2 r1 :=
begin
  rw subtype.ext,
  exact rational_open_data.inter_symm r1.1 r2.1
end

end -- section

open uniform_space

-- rat_open_data is short for "rational open data". KB needs to think more clearly
-- about namespaces etc.

/-- A<T/s>, the functions on D(T,s). A topological ring -/
def rat_open_data_completion (r : rational_open_data A) :=
completion (rational_open_data.localization r)

namespace rat_open_data_completion
open topological_space

/-- The ring structure on A<T/s>. -/
noncomputable instance (r : rational_open_data A) : comm_ring (rat_open_data_completion r) :=
by dunfold rat_open_data_completion; apply_instance

/-- The uniform structure on A<T/s>. -/
instance uniform_space (r : rational_open_data A) : uniform_space (rat_open_data_completion r) :=
by dunfold rat_open_data_completion; apply_instance

/-- A<T/s> is a topological ring. -/
instance (r : rational_open_data A) : topological_ring (rat_open_data_completion r) :=
by dunfold rat_open_data_completion; apply_instance

/-- The natural map A<T₁/s₁> → A<T₂/s₂> for two rational open subsets r1 and r2 with r1 ≤ r2.-/
noncomputable def restriction {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
rat_open_data_completion r1 → rat_open_data_completion r2 :=
completion.map (rational_open_data.localization_map h)

/-- The natural map A<T₁/s₁> → A<T₂/s₂> is a ring homomorphism.-/
instance restriction_is_ring_hom {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
  is_ring_hom (restriction h) :=
completion.is_ring_hom_map (rational_open_data.localization_map_is_cts h)

lemma restriction_is_uniform_continuous {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
uniform_continuous (rat_open_data_completion.restriction h) :=
completion.uniform_continuous_map

end rat_open_data_completion -- namespace

open topological_space

/-- The underlying type of 𝒪_X(U), the structure presheaf on X = Spa(A) -/
def presheaf_value (U : opens (spa A)) :=
{f : Π (rd : rational_open_data_subsets U), rat_open_data_completion rd.1 //
   ∀ (rd1 rd2 : rational_open_data_subsets U) (h : rd1.1 ≤ rd2.1),
     rat_open_data_completion.restriction h (f rd1) = (f rd2)} -- agrees on overlaps

/-- An auxilliary definition:
  The underlying type of 𝒪_X(U), the structure presheaf on X = Spa(A),
  but given as a subset, rather than a subtype.
  This definition is used for the definition of the ring structure on 𝒪_X(U) -/
def presheaf_value_set (U : opens (spa A)) :=
{f : Π (rd : rational_open_data_subsets U), rat_open_data_completion rd.1 |
   ∀ (rd1 rd2 : rational_open_data_subsets U) (h : rd1.1 ≤ rd2.1),
     rat_open_data_completion.restriction h (f rd1) = (f rd2)}

-- We need to check it's a ring

/-- The value of the structure presheaf on an open set U
is a subring of the big Pi-type in its definiton.-/
lemma presheaf_subring (U : opens (spa A)) : is_subring (presheaf_value_set U) :=
{ zero_mem := λ _ _ _, is_ring_hom.map_zero _,
  one_mem := λ _ _ _, is_ring_hom.map_one _,
  add_mem := λ a b ha hb rd₁ rd₂ h,
  begin
    change rat_open_data_completion.restriction h (a rd₁ + b rd₁) = a rd₂ + b rd₂,
    rw is_ring_hom.map_add (rat_open_data_completion.restriction h),
    rw [ha _ _ h, hb _ _ h],
  end,
  neg_mem := λ a ha rd₁ rd₂ h,
  begin
    change rat_open_data_completion.restriction h (-(a rd₁)) = -(a rd₂),
    rw is_ring_hom.map_neg (rat_open_data_completion.restriction h),
    rw ha _ _ h,
  end,
  mul_mem := λ a b ha hb rd₁ rd₂ h,
  begin
    change rat_open_data_completion.restriction h (a rd₁ * b rd₁) = a rd₂ * b rd₂,
    rw is_ring_hom.map_mul (rat_open_data_completion.restriction h),
    rw [ha _ _ h, hb _ _ h]
  end }

/-- The ring structure on the value of the structure presheaf on an open set U.-/
noncomputable instance presheaf_comm_ring (U : opens (spa A)) : comm_ring (presheaf_value U) :=
@subset.comm_ring _ pi.comm_ring _ (spa.presheaf_subring U)

/-- The topology on the value of the structure presheaf on an open set U.-/
instance presheaf_top_space (U : opens (spa A)) : topological_space (presheaf_value U) :=
by unfold presheaf_value; apply_instance

/-- The value of the structure presheaf on an open set U is a topological ring.-/
instance presheaf_top_ring (U : opens (spa A)) : topological_ring (presheaf_value U) :=
begin
  haveI := spa.presheaf_subring U,
  letI : topological_ring (Π (rd : rational_open_data_subsets U), rat_open_data_completion (rd.1)) :=
    by apply_instance,
  apply topological_subring (presheaf_value_set U),
end

/-- The restriction map for the structure presheaf on the adic spectrum of a Huber pair. -/
def presheaf_map {U V : opens (spa A)} (hUV : U ≤ V) :
  presheaf_value V → presheaf_value U :=
λ f, ⟨_, λ rd1 rd2 h,
  (f.2 (rational_open_data_subsets.map hUV rd1)
    (rational_open_data_subsets.map hUV rd2) h : _)⟩

-- Note the (X : _) trick at the end of the preceding definition,
-- which tells Lean "don't try and elaborate X assuming it has the type you know it has,
-- elaborate it independently, figure out the type, and then unify".
-- Thanks to Mario Carneiro for this trick which
-- hugely speeds up elaboration time of this definition.

@[simp] lemma presheaf_map_id (U : opens (spa A)) :
  presheaf_map (le_refl U) = id :=
by { delta presheaf_map, tidy }

lemma presheaf_map_comp {U V W : opens (spa A)} (hUV : U ≤ V) (hVW : V ≤ W) :
  presheaf_map hUV ∘ presheaf_map hVW = presheaf_map (le_trans hUV hVW) :=
by { delta presheaf_map, tidy }

/-- The restriction maps of the structure presheaf are ring homomorphisms. -/
instance presheaf_map_is_ring_hom {U V : opens (spa A)} (hUV : U ≤ V) :
is_ring_hom (presheaf_map hUV) :=
{ map_one := rfl,
  map_mul := λ _ _, rfl,
  map_add := λ _ _, rfl }

lemma presheaf_map_cts {U V : opens (spa A)} (hUV : U ≤ V) :
  continuous (presheaf_map hUV) :=
continuous_subtype_mk _ (continuous_pi (λ i, ((continuous_apply _).comp continuous_subtype_val)))

variable (A)

/-- The structure presheaf on the adic spectrum of a Huber pair. -/
noncomputable def presheaf_of_topological_rings : presheaf_of_topological_rings (spa A) :=
{ F := presheaf_value,
  res := λ U V, presheaf_map,
  Hid := presheaf_map_id,
  Hcomp := λ U V W, presheaf_map_comp,
  Fring := spa.presheaf_comm_ring,
  res_is_ring_hom := λ U V, spa.presheaf_map_is_ring_hom,
  Ftop := spa.presheaf_top_space,
  Ftop_ring := spa.presheaf_top_ring,
  res_continuous := λ U V, presheaf_map_cts }

end spa -- namespace

-- notes

-- KB idle comment: I guess we never make A<T/s> a Huber pair if A is a Huber pair?
-- We would need integral closure for this and I don't think we have it in mathlib.

-- We see mid way through p75 that the definition of the presheaf
-- on V is proj lim of O_X(U) as U runs through rationals opens in V. This gets
-- the projective limit topology and then we have a presheaf (hopefully this is
-- straightforward) of complete topological rings (need proj lim of complete is complete)





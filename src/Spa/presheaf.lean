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

def rational_open_data_subsets (U : opens (spa A)) :=
{ r : rational_open_data A // r.open_set ⊆ U}

def rational_open_data_subsets.map {U V : opens (spa A)} (hUV : U ≤ V)
  (rd : rational_open_data_subsets U) :
  rational_open_data_subsets V :=
⟨rd.val, set.subset.trans rd.property hUV⟩

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

instance (r : rational_open_data A) : uniform_space (rational_open_data.localization r) :=
topological_add_group.to_uniform_space _

instance (rd : rational_open_data A): uniform_add_group (rational_open_data.localization rd) :=
topological_add_group_is_uniform

def localization_map_is_uniform_continuous {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
  uniform_continuous (rational_open_data.localization_map h) :=
uniform_continuous_of_continuous (rational_open_data.localization_map_is_cts h)

end -- section

open uniform_space

-- rat_open_data is short for "rational open data". KB needs to think more clearly
-- about namespaces etc.
/-- A<T/s>, the functions on D(T,s). A topological ring -/
def rat_open_data_completion (r : rational_open_data A) :=
completion (rational_open_data.localization r)

namespace rat_open_data_completion
open topological_space

noncomputable instance (r : rational_open_data A) : comm_ring (rat_open_data_completion r) :=
by dunfold rat_open_data_completion; apply_instance

instance uniform_space (r : rational_open_data A) : uniform_space (rat_open_data_completion r) :=
by dunfold rat_open_data_completion; apply_instance

instance (r : rational_open_data A) : topological_ring (rat_open_data_completion r) :=
by dunfold rat_open_data_completion; apply_instance

noncomputable def restriction {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
rat_open_data_completion r1 → rat_open_data_completion r2 :=
completion.map (rational_open_data.localization_map h)

instance restriction_is_ring_hom {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
  is_ring_hom (restriction h) :=
completion.is_ring_hom_map (rational_open_data.localization_map_is_cts h)

lemma restriction_is_uniform_continuous {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
uniform_continuous (rat_open_data_completion.restriction h) :=
completion.uniform_continuous_map

end rat_open_data_completion -- namespace

open topological_space

/-- The underlying type of 𝒪_X(U), the structure presheaf on Spa(A) -/
def presheaf_value (U : opens (spa A)) :=
{f : Π (rd : rational_open_data_subsets U), rat_open_data_completion rd.1 //
   ∀ (rd1 rd2 : rational_open_data_subsets U) (h : rd1.1 ≤ rd2.1),
     rat_open_data_completion.restriction h (f rd1) = (f rd2)} -- agrees on overlaps

def presheaf_value_set (U : opens (spa A)) :=
{f : Π (rd : rational_open_data_subsets U), rat_open_data_completion rd.1 |
   ∀ (rd1 rd2 : rational_open_data_subsets U) (h : rd1.1 ≤ rd2.1),
     rat_open_data_completion.restriction h (f rd1) = (f rd2)}

-- We need to check it's a ring


instance presheaf_subring (U : opens (spa A)) : is_subring (presheaf_value_set U) :=
begin
refine {..},
  { -- zero_mem
    intros rd₁ rd₂ h,
    exact is_ring_hom.map_zero _ },
  { -- add_mem
    intros a b ha hb rd₁ rd₂ h,
    change rat_open_data_completion.restriction h (a rd₁ + b rd₁) = a rd₂ + b rd₂,
    rw is_ring_hom.map_add (rat_open_data_completion.restriction h),
    rw [ha _ _ h, hb _ _ h] },
  { -- neg_mem
    intros a ha rd₁ rd₂ h,
    change rat_open_data_completion.restriction h (-(a rd₁)) = -(a rd₂),
    rw is_ring_hom.map_neg (rat_open_data_completion.restriction h),
    rw ha _ _ h },
  { -- one_mem
    intros rd₁ rd₂ h,
    exact is_ring_hom.map_one _ },
  { -- mul_mem
    intros a b ha hb rd₁ rd₂ h,
    change rat_open_data_completion.restriction h (a rd₁ * b rd₁) = a rd₂ * b rd₂,
    rw is_ring_hom.map_mul (rat_open_data_completion.restriction h),
    rw [ha _ _ h, hb _ _ h] }
end

noncomputable instance presheaf_comm_ring (U : opens (spa A)) : comm_ring (presheaf_value U) :=
begin
  apply @subset.comm_ring _ pi.comm_ring _ _, apply_instance,
  exact spa.presheaf_subring U
end

instance presheaf_top_space (U : opens (spa A)) : topological_space (presheaf_value U) :=
by unfold presheaf_value; apply_instance

example (U : opens (spa A)) :
  topological_ring (Π (rd : rational_open_data_subsets U), rat_open_data_completion (rd.1)) :=
by apply_instance

-- tactic mode because I can't get Lean to behave. Note: switching to tactic
-- mode indicated the problem was that Lean was not finding the two instances I flag
-- with haveI and letI; probably now I know this one could try to go back into term mode.
instance presheaf_top_ring (U : opens (spa A)) : topological_ring (presheaf_value U) :=
begin
  haveI := spa.presheaf_subring U,
  letI : topological_ring (Π (rd : rational_open_data_subsets U), rat_open_data_completion (rd.1)) :=
    by apply_instance,
  apply topological_subring (presheaf_value_set U),
end

instance (U : opens (spa A)) (r : rational_open_data_subsets U) :
  is_ring_hom (λ (f : presheaf_value U), f.val r) :=
{ map_one := rfl,
  map_mul := λ _ _, rfl,
  map_add := λ _ _, rfl }

-- note the (X : _) trick, which tells Lean "don't try and
-- elaborate X assuming it has the type you know it has,
-- elaborate it independently, figure out the type, and
-- then unify". Thanks to Mario Carneiro for this trick which
-- hugely speeds up elaboration time of this definition.
def presheaf_map {U V : opens (spa A)} (hUV : U ≤ V) :
  presheaf_value V → presheaf_value U :=
λ f, ⟨_, λ rd1 rd2 h,
  (f.2 (rational_open_data_subsets.map hUV rd1)
    (rational_open_data_subsets.map hUV rd2) h : _)⟩

lemma presheaf_map_id (U : opens (spa A)) :
  presheaf_map (le_refl U) = id :=
by { delta presheaf_map, tidy }

lemma presheaf_map_comp {U V W : opens (spa A)} (hUV : U ≤ V) (hVW : V ≤ W) :
  presheaf_map hUV ∘ presheaf_map hVW = presheaf_map (le_trans hUV hVW) :=
by { delta presheaf_map, tidy }

instance presheaf_map_is_ring_hom {U V : opens (spa A)} (hUV : U ≤ V) :
is_ring_hom (presheaf_map hUV) :=
{ map_one := rfl,
  map_mul := λ _ _, rfl,
  map_add := λ _ _, rfl }

def presheaf_map_cts {U V : opens (spa A)} (hUV : U ≤ V) :
  continuous (presheaf_map hUV) :=
continuous_subtype_mk _ (continuous_pi (λ i, ((continuous_apply _).comp continuous_subtype_val)))

variable (A)

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

end spa -- namespace I think

-- old notes

-- remember that a rational open is not actually `rational_open s T` in full
-- generality -- we also need that T is finite and that T generates an open ideal in A.
-- The construction on p73/74 (note typo in first line of p74 -- ideal should be I.D)
-- gives A<T/s> (need completion) and A<T/s>^+ (need integral closure).

-- KB idle comment: I guess we never make A<T/s> a Huber pair if A is a Huber pair?
-- We would need integral closure for this and I don't think we have it in mathlib.

-- We see mid way through p75 that the definition of the presheaf
-- on V is proj lim of O_X(U) as U runs through rationals opens in V. This gets
-- the projective limit topology and then we have a presheaf (hopefully this is
-- straightforward) of complete topological rings (need proj lim of complete is complete)


#sanity_check
#doc_blame



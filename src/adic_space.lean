import for_mathlib.prime
import for_mathlib.is_cover 
import analysis.topology.topological_structures
import data.nat.prime 
import algebra.group_power
import for_mathlib.presheaves
import for_mathlib.topology

open nat function

section comm_ring
variables (R : Type) [comm_ring R]
-- This section is filled in in Johan's PR
definition is_subring {R : Type} [comm_ring R] : set R → Prop := sorry 
definition is_integrally_closed {R : Type} [comm_ring R] : set R → Prop := sorry  
end comm_ring

section topological_ring

variables (R : Type*) [comm_ring R] [topological_space R] [topological_ring R]  

def nhd_zero := (nhds (0 : R)).sets
variable {R}
lemma nhd_zero_symmetric {V : set R} : V ∈ nhd_zero R →  (λ a, -a) '' V ∈ nhd_zero R :=
begin
  intro H,
  have := continuous.tendsto (topological_add_group.continuous_neg R) 0,
  rw (show (λ (a : R), -a) 0 = 0, by simp) at this,
  have almost:= this H,
  have aux : { r : R | -r ∈ V } = (λ a, -a) '' V, by simp[set.image, neg_eq_iff_neg_eq],
  simpa [filter.mem_map, aux] using almost
end

-- peredicates we need for topological rings

-- Following is copy-pasted from t2_space class.
-- We need to think whether we could directly use that class
definition is_hausdorff (α : Type*) [topological_space α] : Prop := 
  ∀x y, x ≠ y → ∃u v : set α, is_open u ∧ is_open v ∧ x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅


open filter lattice
lemma half_nhd {α : Type*} [topological_space α] [add_group α] [topological_add_group α] (U ∈ (nhds (0 : α)).sets) : 
  ∃ V ∈ (nhds (0 : α)).sets, ∀ v w ∈ V, v + w ∈ U :=
/- Here is the story : by continuity of addition, and because 0 + 0 = 0,
   (+)⁻¹(U) is a neighborhood of (0, 0). Hence it contains some V₁ × V₂. Then set V = V₁ ∩ V₂ -/
begin
  have nhdb_in_prod : ((λ a : α × α, a.1+a.2)⁻¹' U) ∈ (nhds ((0, 0) : α × α)).sets,
    by apply tendsto_add' ; simp [H],
  rw nhds_prod_eq at nhdb_in_prod,
  rcases mem_prod_iff.1 nhdb_in_prod with ⟨V₁, H₁, V₂, H₂, H⟩,
  have H12: V₁ ∩ V₂ ∈ (nhds (0 : α)).sets := inter_mem_sets H₁ H₂,    
  existsi [(V₁ ∩ V₂), H12],
  intros v w Hv Hw,
  have : (v,w) ∈ set.prod V₁ V₂, by finish,
  simpa using H this
end


instance toplogical_ring.to_uniform_space : uniform_space R := 
uniform_space.of_core { 
  uniformity  := (⨅ U ∈ nhd_zero R, principal {p : R×R | p.2 - p.1 ∈ U}),
  refl        := begin simp, intros i H r, exact mem_of_nhds H end,
  symm        := tendsto_infi.2 $ assume V, tendsto_infi.2 $ assume h,
    tendsto_infi' ((λ r, -r) '' V)
      begin 
        simp [nhd_zero_symmetric h],
        unfold tendsto,
        rw map_principal,
        have H : prod.swap '' {p : R × R | ∃ (x : R), x ∈ V ∧ -x = p.snd + -p.fst} = {p : R × R | p.snd - p.fst ∈ V},
        begin 
          rw set.image_swap_eq_preimage_swap,
          ext p,
          cases p with r1 r2,
          change (∃ x, x ∈ V ∧ -x = r1 - r2) ↔ (r2 - r1 ∈ V),
          have : ∀ x, -x = r1 - r2 ↔ x = r2 - r1,
            by intro x; rw [neg_eq_iff_neg_eq, eq_comm]; simp,
          simp only [this], simp
      end,
      simp [H],                           
    end,
  comp        := le_infi $ assume V, le_infi $ assume H, 
    begin
      rcases half_nhd V H with ⟨U, ⟨h, h'⟩⟩,
      have comprel : comp_rel {p : R × R | p.snd - p.fst ∈ U} {p : R × R | p.snd - p.fst ∈ U} ⊆ {p : R × R | p.snd - p.fst ∈ V},
      begin
        intros p p_comp_rel,
        rcases p_comp_rel with ⟨z, ⟨Hz1, Hz2⟩⟩,
        simpa using h' _ _ Hz1 Hz2,
      end,
      replace comprel : principal (comp_rel {p : R × R | p.snd - p.fst ∈ U} {p : R × R | p.snd - p.fst ∈ U}) ≤ principal {p : R × R | p.snd - p.fst ∈ V},
        simpa using comprel,
      apply lift'_le,
      swap,
      exact comprel,
      apply mem_infi_sets U,
      apply mem_infi_sets h,
      simp
    end }

variable (R)
/-- Wedhorn Definition 5.31 page 38 -/
definition is_complete : Prop := is_hausdorff R ∧ ∀ {f:filter R}, cauchy f → ∃x, f ≤ nhds x

variable {R}
/-- Wedhorn Definition 5.27 page 36 -/
definition is_bounded 
  (B : set R) : Prop := ∀ U ∈ nhd_zero R, ∃ V ∈ nhd_zero R, ∀ v ∈ V, ∀ b ∈ B, v*b ∈ U

def power_set (r : R) : set R := set.range (λ n : ℕ, r^n)

definition is_power_bounded (r : R) : Prop := is_bounded (power_set r)

variable (R)
-- Somehow we need R° both as a subset of R and a subtype. 
-- There is a coercion from the set to the subtype but relying naively on it seems to bring 
-- type class resolution issues
definition power_bounded_subring := {r : R // is_power_bounded r}
definition power_bounded_subring_set := {r : R | is_power_bounded r}

instance power_bounded_subring_to_ring : has_coe (power_bounded_subring R) R := ⟨subtype.val⟩ 
instance power_bounded_subring_is_ring  : comm_ring (power_bounded_subring R) := sorry
instance : topological_space (power_bounded_subring R) := sorry
instance : topological_ring (power_bounded_subring R) := sorry

definition is_uniform : Prop := is_bounded (power_bounded_subring_set R)

theorem p_is_power_bounded [p : Prime] : is_power_bounded (p : power_bounded_subring R) := sorry

variable {R}
definition is_pseudo_uniformizer : R → Prop := sorry
end topological_ring

-- Schol= : "Recall that a topological ring R is Tate if it contains an
-- open and bounded subring R0 ⊂ R and a topologically nilpotent unit pi ∈ R; such elements are
-- called pseudo-uniformizers.""
-- we need definitions of bounded subsete and topologically nilpotent -- and do we have unit? Probably.
class Tate_ring (R : Type) extends comm_ring R, topological_space R, topological_ring R :=
(unfinished : sorry)

-- f-adic rings are called Huber rings by Scholze.
-- Topological ring A contains on open subring A0 such that the subspace topology on A0 is
-- I-adic, where I is a finitely generated ideal of A0 .
class Huber_ring (R : Type) extends comm_ring R, topological_space R, topological_ring R :=
(unfinished2 : sorry)

-- TODO should have an instance going from Tate to Huber


-- Wedhorn Def 7.14
structure is_ring_of_integral_elements {R : Type} [Huber_ring R] (Rplus : set R) : Prop :=
[is_subring : is_subring Rplus]
(is_open : is_open Rplus)
(is_int_closed : is_integrally_closed Rplus)
(is_power_bounded : Rplus ⊆ { r : R | is_power_bounded r})

-- a Huber Ring is an f-adic ring.
-- a Huber Pair is what Huber called an Affinoid Ring.
structure Huber_pair :=
(R : Type) 
[RHuber : Huber_ring R]
(Rplus : set R)
[intel : is_ring_of_integral_elements Rplus]

instance : has_coe_to_sort Huber_pair := 
{ S := Type, coe := Huber_pair.R}

postfix `⁺` : 66 := λ R : Huber_pair _, R.Rplus  

definition Spa (A : Huber_pair) : Type := sorry
instance Spa_topology (A : Huber_pair) : topological_space (Spa A) := sorry 

--definition 𝓞_X (A : Huber_pair) : presheaf_of_rings (Spa A) := sorry 
-- it's a presheaf of complete topological rings on all opens (defined on rational opens
-- first and then extended to all via proj limits) -- Huber p75
-- most of that would not be in the adic_space file.

--structure 𝓥pre :=
--(X : sorry)
--(𝓞X : sorry)
--(v : sorry)

/-
We denote by 𝓥pre the category of tuples X = (X, O X , (v x ) x∈X ), where
(a) X is a topological space,
(b) 𝓞_X is a presheaf of complete topological rings on X such that the stalk 𝓞_X,x of
𝓞_X (considered as a presheaf of rings) is a local ring,
(c) v_x is an equivalence class of valuations on the stalk 𝓞_X,x such that supp(v_x) is the
maximal ideal of 𝓞_X,x .

Wedhorn p76 shows how Spa(A) gives an object of this for A a Huber pair
-/

--definition affinoid_adic_space (A : Huber_pair) : 𝓥pre := sorry

-- unwritten -- it's a full subcat of 𝓥pre
class preadic_space (X : Type) extends topological_space X 

-- not logically necessary but should be easy
instance (A : Huber_pair) : preadic_space (Spa A) := sorry 

-- attribute [class] _root_.is_open 

instance preadic_space_restriction {X : Type} [preadic_space X] {U : opens X} :
  preadic_space U := sorry

-- unwritten 
class adic_space (X : Type) extends preadic_space X

-- a preadic_space_equiv is just an isom in 𝓥pre, or an isomorphism of preadic spaces.
-- is homeo in Lean yet?
-- unwritten
structure preadic_space_equiv (X Y : Type) [AX : preadic_space X] [AY : preadic_space Y] extends equiv X Y

definition is_preadic_space_equiv (X Y : Type) [AX : preadic_space X] [AY : preadic_space Y] := 
  nonempty (preadic_space_equiv X Y)

definition preadic_space_pullback {X : Type} [preadic_space X] (U : set X) := {x : X // x ∈ U}

instance pullback_is_preadic_space {X : Type} [preadic_space X] (U : set X) : preadic_space (preadic_space_pullback U) := sorry 

-- notation `is_open` := _root_.is_open

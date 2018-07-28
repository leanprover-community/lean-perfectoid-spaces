import for_mathlib.add_subgroup group_theory.submonoid
import data.polynomial
import algebra.ring
import analysis.topology.topological_structures

local attribute [instance] classical.prop_decidable
universes u v

open group

variables {R : Type u} [ring R]

/-- `S` is a subring: a set containing 1 and closed under multiplication, addition and and additive inverse. -/
class is_subring  (S : set R) extends is_add_subgroup S, is_submonoid S : Prop.

variables {S : set R} [is_subring S]

instance subset.ring : ring S :=
{ add_comm      := assume ⟨a,_⟩ ⟨b,_⟩, subtype.eq $ add_comm _ _,
  left_distrib  := assume ⟨a,_⟩ ⟨b,_⟩ ⟨c,_⟩, subtype.eq $ left_distrib _ _ _,
  right_distrib := assume ⟨a,_⟩ ⟨b,_⟩ ⟨c,_⟩, subtype.eq $ right_distrib _ _ _,
  .. subtype.add_group,
  .. subtype.monoid }

instance subset.comm_ring {R : Type} [comm_ring R] {S : set R} [is_subring S] : comm_ring S :=
{ mul_comm := assume ⟨a,_⟩ ⟨b,_⟩, subtype.eq $ mul_comm _ _,
  .. subset.ring }

instance subtype.ring : ring (subtype S) := subset.ring
instance subtype.comm_ring {R : Type} [comm_ring R] {S : set R} [is_subring S] : comm_ring (subtype S) := subset.comm_ring

namespace is_ring_hom

instance {S : set R} [is_subring S] : is_ring_hom (@subtype.val R S) :=
{ map_add := λ _ _, rfl,
  map_mul := λ _ _, rfl,
  map_one := rfl }

end is_ring_hom

variables {cR : Type u} [comm_ring cR]

instance subset.comm_ring {S : set cR} [is_subring S] : comm_ring S :=
{ mul_comm := λ ⟨a,_⟩ ⟨b,_⟩, subtype.eq $ mul_comm _ _,
  ..subset.ring
}

instance subtype.comm_ring {S : set cR} [is_subring S] : comm_ring (subtype S) := subset.comm_ring

variables [decidable_eq R]
 
noncomputable def polynomial.map {S : Type v} [comm_ring S] (f : S → cR) [is_ring_hom f] : polynomial S → polynomial cR :=
finsupp.map_range f (is_ring_hom.map_zero f)

def is_integral (S : set cR) [is_subring S] (r : cR) : Prop := 
∃ f : polynomial ↥S, (polynomial.monic f) ∧ polynomial.eval r (@polynomial.map cR _ ↥S _ (subtype.val) is_ring_hom.is_ring_hom f) = 0

def is_integrally_closed (S : set R) [is_subring S] :=
∀ r : R, (is_integral S r) → r ∈ S

section topological_subring

variables [topological_space R] [topological_ring R]
variables {S : set R} [is_subring S]

instance subring.topological_space : topological_space S := by apply subtype.topological_space
instance subring.topological_ring : topological_ring S :=
{ continuous_add :=
  begin
    refine continuous_subtype_mk _ _,
    rw show (λ (p : ↥S × ↥S), ↑(p.fst) + ↑(p.snd)) = function.comp (λ p : R × R, p.fst + p.snd) (λ p : ↥S × ↥S, (↑p.fst,↑p.snd)),
    by simp [function.comp],
    exact continuous.comp
            (continuous.prod_mk
              (continuous.comp continuous_fst continuous_subtype_val)
              (continuous.comp continuous_snd continuous_subtype_val))
            (topological_add_monoid.continuous_add R),
  end,
  continuous_mul :=
  begin
    refine continuous_subtype_mk _ _,
    rw show (λ (p : ↥S × ↥S), ↑(p.fst) * ↑(p.snd)) = function.comp (λ p : R × R, p.fst * p.snd) (λ p : ↥S × ↥S, (↑p.fst,↑p.snd)),
    by simp [function.comp],
    exact continuous.comp
            (continuous.prod_mk
              (continuous.comp continuous_fst continuous_subtype_val)
              (continuous.comp continuous_snd continuous_subtype_val))
            (topological_monoid.continuous_mul R),
  end,
  continuous_neg := 
  begin
    apply continuous_subtype_mk,
    apply continuous.comp continuous_subtype_val (topological_add_group.continuous_neg R),
  end,
  .. subtype.ring,
  .. subring.topological_space }

end topological_subring

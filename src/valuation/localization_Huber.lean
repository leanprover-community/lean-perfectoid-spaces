-- Extending continuous valuations on Huber rings R to rational localizations R(T/s)
-- and their completions.
-- Note that this file comes much lower down the import tree
-- than stuff like valuation.canonical and valuation.field.
-- Here we use all this Huber ring stuff like R(T/s).

import valuation.localization
import valuation.topology
import Huber_ring.localization
import Spa

noncomputable theory

variables {A : Huber_pair}
{Γ : Type*} [linear_ordered_comm_group Γ] {v : valuation A Γ}
{rd : spa.rational_open_data A} (hv : valuation.is_continuous v)

namespace Huber_pair
open valuation

local attribute [instance] set.pointwise_mul_action

local notation `ATs` := spa.rational_open_data.localization rd
local notation `s` := rd.s
local notation `T` := rd.T

--noncomputable instance valuation_field.ring_with_zero_nhd : ring_with_zero_nhd (valuation_field v) :=
--valuation.ring_with_zero_nhd (on_valuation_field v : valuation (valuation_field v) Γ)

def unit_lemma (hs : v s ≠ 0) : is_unit (valuation_field_mk v s) :=
is_unit_of_mul_one _ (valuation_field_mk v s)⁻¹ $ mul_inv_cancel $
  valuation_field_mk_ne_zero v s hs

-- TODO? : change Huber_ring.away.lift so that instead of asking for an implicit unit
-- whose inv is f s, it just asks for is_unit f s. Or at least a unit whose val is f s...
noncomputable def unit_s (hs : v s ≠ 0) : units (valuation_field v) :=
classical.some (unit_lemma hs)

lemma unit_aux (hs : v s ≠ 0) : ((unit_s hs)⁻¹).inv = valuation_field_mk v s
:= (classical.some_spec (unit_lemma hs)).symm

example : (λ r, localization.of (valuation_ID_mk v r)) = valuation_field_mk v := rfl

def v_T_over_s (hs : v s ≠ 0) : set (valuation_field v) :=
(unit_s hs).inv • ((valuation_field_mk v) '' rd.T)

lemma v_T_over_s_le_one (hs : v s ≠ 0) (hT2 : ∀ t : A, t ∈ T → v t ≤ v s) :
  v_T_over_s hs ⊆ {x : valuation_field v | valuation_field.canonical_valuation v x ≤ 1} :=
begin
  let v' := valuation_field.canonical_valuation v,
  intros k Hk,
  show v' k ≤ 1,
  let u := unit_s hs,
  have remember_this : u.val = valuation_field_mk v s := unit_aux hs,
  unfold v_T_over_s at Hk,
  rw set.mem_smul_set at Hk,
  rcases Hk with ⟨l, Hl, rfl⟩,
  rw v'.map_mul,
  rcases Hl with ⟨t, ht, rfl⟩,
  change v' (↑(unit_s hs)⁻¹) * _ ≤ _,
  rw mul_comm,
  apply with_zero.le_of_le_mul_right (unit_is_not_none v' u),
  rw [mul_assoc, one_mul, ←v'.map_mul, units.inv_mul, v'.map_one, mul_one],
  change canonical_valuation v t ≤ v' u.val,
  rw remember_this,
  change _ ≤ canonical_valuation v s,
  rw canonical_valuation_is_equiv v,
  exact hT2 _ ht,
end

lemma v_le_one_is_bounded {R : Type*} [comm_ring R] (v : valuation R Γ) :
  is_bounded {x : valuation_field v | valuation_field.canonical_valuation v x ≤ 1} :=
begin
  let v' := valuation_field.canonical_valuation v,
  intros U HU,
  rw is_subgroups_basis.nhds_zero at HU,
  rcases HU with ⟨γ, HU⟩,
  let V := {k : valuation_field v | v' k < ↑γ},
  use V,
  existsi _, swap,
  { apply mem_nhds_sets,
      apply is_subgroups_basis.is_op,
    show v' 0 < γ,
    rw v'.map_zero,
    exact with_zero.zero_lt_some
  },
  intros w Hw b Hb,
  change V ⊆ U at HU,
  change v' w < γ at Hw,
  change v' b ≤ 1 at Hb,
  apply set.mem_of_mem_of_subset _ HU,
  change v' (w * b) < γ,
  rw v'.map_mul,
  exact actual_ordered_comm_monoid.mul_lt_of_lt_of_nongt_one' Hw Hb,
end

lemma v_le_one_is_power_bounded {R : Type*} [comm_ring R] (v : valuation R Γ) :
  is_power_bounded_subset {x : valuation_field v | valuation_field.canonical_valuation v x ≤ 1} :=
begin
  let v' := valuation_field.canonical_valuation v,
  refine is_bounded_subset _ _ _ (v_le_one_is_bounded v),
  intros x hx,
  induction hx with a ha a b ha' hb' ha hb,
  { assumption },
  { show v' 1 ≤ 1,
    rw v'.map_one,
    exact le_refl _
  },
  { show v' (a * b) ≤ 1,
    rw v'.map_mul,
    exact actual_ordered_comm_monoid.mul_nongt_one' ha hb,
  }
end

lemma v_T_over_s_is_power_bounded (hs : v s ≠ 0) (hT2 : ∀ t : A, t ∈ T → v t ≤ v s) :
  is_power_bounded_subset (v_T_over_s hs) :=
begin
  apply power_bounded.subset (v_T_over_s_le_one hs hT2),
  exact v_le_one_is_power_bounded v
end

noncomputable def to_valuation_field (hs : v s ≠ 0) : ATs → (valuation_field v) :=
Huber_ring.away.lift T s (unit_aux hs)

instance (hs : v s ≠ 0) : is_ring_hom (to_valuation_field hs) :=
by delta to_valuation_field; apply_instance

local attribute [instance] valuation.subgroups_basis

theorem to_valuation_field_cts' (hs : v s ≠ 0)(hT2 : ∀ t : A, t ∈ T → v t ≤ v s) (hv : is_continuous v) :
  continuous (to_valuation_field hs) :=
Huber_ring.away.lift_continuous T s (is_subgroups_basis.nonarchimedean _)
  (continuous_valuation_field_mk_of_continuous v hv) (unit_aux hs) (rd.Hopen)
  (v_T_over_s_is_power_bounded hs hT2)

-- now we need that the triangles commute when we fix v but change s.

theorem to_valuation_field_commutes (r1 r2 : spa.rational_open_data A) (h : r1 ≤ r2)
  (hs1 : v r1.s ≠ 0) (hs2 : v r2.s ≠ 0) :
to_valuation_field hs1 = (to_valuation_field hs2) ∘ (spa.rational_open_data.localization_map h) :=
begin
  refine localization.funext
    (to_valuation_field hs1 : localization A.R (powers r1.s) → valuation_field v)
    ((to_valuation_field hs2) ∘ (spa.rational_open_data.localization_map h) :
      localization A.R (powers r1.s) → valuation_field v) _,
  intro r,
  change Huber_ring.away.lift (r1.T) (r1.s) _ (localization.of r) =
    Huber_ring.away.lift (r2.T) (r2.s) _ (spa.rational_open_data.localization_map h (localization.of r)),
  dunfold spa.rational_open_data.localization_map,
  rw Huber_ring.away.lift_of,
  rw Huber_ring.away.lift_of,
  change _ = Huber_ring.away.lift (r2.T) (r2.s) _ (localization.of r),
  rw Huber_ring.away.lift_of,
end

namespace rational_open_data

lemma to_valuation_field_cts_aux {r : spa.rational_open_data A} {v : spa A}
(hv : v ∈ r.rational_open) : (Spv.out v.1) (r.s) ≠ 0 := hv.2

def to_valuation_field {r : spa.rational_open_data A} {v : spa A} (hv : v ∈ r.rational_open) :
  spa.rational_open_data.localization r → valuation_field (Spv.out (v.val)) :=
(to_valuation_field $ to_valuation_field_cts_aux hv)

instance {r : spa.rational_open_data A} {v : spa A} (hv : v ∈ r.rational_open) :
  is_ring_hom (to_valuation_field hv) := by {delta to_valuation_field, apply_instance}

/-- If v : spa A is in D(T,s) then the map A(T/s) -> K_v is continuous -/
theorem to_valuation_field_cts {r : spa.rational_open_data A} {v : spa A}
  (hv : v ∈ r.rational_open) : continuous (to_valuation_field hv) :=
Huber_pair.to_valuation_field_cts' hv.2 hv.1 v.2.1

-- Now we need to show that if r1 <= r2 then these to_valuation_field maps
-- are compatible.

theorem to_valuation_field_commutes {r1 r2 : spa.rational_open_data A} {v : spa A}
  (hv1 : v ∈ r1.rational_open) (hv2 : v ∈ r2.rational_open) (h : r1 ≤ r2) :
(to_valuation_field hv1) = (to_valuation_field hv2) ∘ (spa.rational_open_data.localization_map h) :=
to_valuation_field_commutes r1 r2 h hv1.2 hv2.2

end rational_open_data

end Huber_pair

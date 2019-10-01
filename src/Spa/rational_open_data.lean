import for_mathlib.group -- some stupid lemma about units

import Spa.space
import Huber_ring.localization

/-!
# Rational open subsets and their properties

We define a preorder on `rational_open_data` that will be used when
constructing the valuations on the stalks of the structure presheaf.
-/

open_locale classical
local attribute [instance] set.pointwise_mul_comm_semiring
local attribute [instance] set.pointwise_mul_action

local postfix `⁺` : 66 := λ A : Huber_pair, A.plus

namespace spa
open set algebra
variables {A : Huber_pair}

namespace rational_open_data
variables (r : rational_open_data A)

/-
The correct preorder on rational open data:

def correct_preorder : preorder (rational_open_data A) :=
{ le := λ r1 r2, rational_open r1 ⊆ rational_open r2,
  le_refl := λ _ _, id,
  le_trans := λ _ _ _, subset.trans,
}

One can prove (in maths) that r1 ≤ r2 iff there's a continuous R-algebra morphism
of Huber pairs localization r2 → localization r1. I think the ← direction of this
iff is straightforward (but I didn't think about it too carefully). However we
definitely cannot prove the → direction of this iff in this repo yet because we
don't have enough API for cont. Here is an indication
of part of the problem. localization r2 is just A[1/r2.s]. But we cannot prove yet r2.s is
invertible in localization.r1, even though we know it doesn't canish anywhere on
rational_open r2 and hence on rational_open r1, because the fact that it doesn't vanish anywhere
on rational_open r1 only means that it's not in any prime ideal corresponding
to a *continuous* valuation on localization r1 which is bounded by 1 on some + subring;
one would now need to prove, at least, that every maximal ideal
is the support of a continuous valuation, which is Wedhorn 7.52(2). This is not
too bad -- but it is work that we have not yet done. However this is by no means the whole story;
we would also need that r1.T is power-bounded in localization.r2
and this looks much worse: it's Wedhorn 7.52(1). Everything is do-able, but it's just *long*.
Long as in "thousands more lines of code". We will need a good theory of primary and
secondary specialisation of valuations and so on and so on. None of this is there at
the time of writing, although I see no obstruction to putting it there, other than the
fact that it would take weeks of work.

We have to work with a weaker preorder then, because haven't made a good enough
API for continuous valuations. We basically work with the preorder r1 ≤ r2 iff
there's a continuous R-algebra map localization r2 → localization r1, i.e, we
define our way around the problem. We are fortunate in that we can prove
(in maths) that the projective limit over this preorder agrees with the projective
limit over the correct preorder.
-/

instance : preorder (rational_open_data A) :=
{ le := λ r1 r2, ∃ k : A, r1.s * k = r2.s ∧
    ∀ t₁ ∈ r1.T, ∃ t₂ ∈ r2.T, ∃ N : ℕ, r2.s ^ N * t₂ = r2.s ^ N * (t₁ * k),
  le_refl := λ r, ⟨1, mul_one _, λ t ht, ⟨t, ht, 0, by rw mul_one⟩⟩,
  le_trans := λ a b c ⟨k, hk, hab⟩ ⟨l, hl, hbc⟩, ⟨k * l, by rw [←mul_assoc, hk, hl], λ ta hta,
  begin
    rcases hab ta hta with ⟨tb, htb, Nab, h1⟩,
    rcases hbc tb htb with ⟨hc, htc, Nbc, h2⟩,
    refine ⟨hc, htc, (Nab + Nbc), _⟩,
    rw [←mul_assoc, pow_add, mul_assoc, h2, ←hl, mul_pow, mul_pow],
    rw (show b.s ^ Nab * l ^ Nab * (b.s ^ Nbc * l ^ Nbc * (tb * l)) =
      b.s ^ Nab * tb * (l ^ Nab * (b.s ^ Nbc * l ^ Nbc *  l)), by ring),
    rw h1,
    ring
  end⟩ }

lemma le_inter_left (r1 r2 : rational_open_data A) :
  r1 ≤ (inter r1 r2) :=
begin
  refine ⟨r2.s, rfl, _⟩,
  intros t1 ht1,
  refine ⟨t1 * r2.s, ⟨t1, mem_insert_of_mem _ ht1, r2.s, mem_insert_s _, rfl⟩, 0, by simp⟩,
end

lemma le_inter_right (r1 r2 : rational_open_data A) :
  r2 ≤ (inter r1 r2) :=
by { rw inter_symm, apply le_inter_left, }

-- The preorder defined above is weaker than the preorder we're supposed to have but don't.
-- However the projective limit we take over our preorder is provably (in maths) equal to
-- the projective limit that we cannot even formalise. The thing we definitely need
-- is that if r1 ≤ r2 then there's a map localization r1 → localization r2

def localization (r : rational_open_data A) := Huber_ring.away r.T r.s

namespace localization

instance : comm_ring (localization r) :=
by unfold localization; apply_instance

instance : subgroups_basis (localization r) :=
Huber_ring.away.top_loc_basis r.T r.s r.Hopen

instance : topological_space (localization r) :=
subgroups_basis.topology _

instance : topological_ring (localization r) :=
ring_filter_basis.is_topological_ring _ rfl

instance : algebra A (localization r) := Huber_ring.away.algebra r.T r.s

instance : has_coe A (localization r) := ⟨λ a, (of_id A (localization r) : A → localization r) a⟩

lemma nonarchimedean (r : rational_open_data A) :
  topological_add_group.nonarchimedean (localization r) :=
subgroups_basis.nonarchimedean

def power_bounded_data (r : rational_open_data A) : set (localization r) :=
let s_inv : localization r :=
  ((localization.to_units ⟨r.s, ⟨1, by simp⟩⟩)⁻¹ : units (localization r)) in
(s_inv • of_id A (localization r) '' r.T)

set_option class.instance_max_depth 38

theorem power_bounded (r : rational_open_data A) :
  is_power_bounded_subset (power_bounded_data r) :=
begin
  suffices : is_bounded (ring.closure (power_bounded_data r)),
  { exact is_bounded.subset add_group.subset_closure this },
  intros U hU,
  rcases subgroups_basis.mem_nhds_zero.mp hU with ⟨_, ⟨V, rfl⟩, hV⟩,
  refine ⟨_, mem_nhds_sets (subgroups_basis.is_op _ rfl (set.mem_range_self _)) _, _⟩,
  { exact V },
  { erw submodule.mem_coe,
    convert submodule.zero_mem _ },
  { intros v hv b hb,
    apply hV,
    rw [mul_comm, ← smul_eq_mul],
    rw submodule.mem_coe at hv ⊢,
    convert submodule.smul_mem _ _ hv,
    swap, { exact ⟨b, hb⟩ }, { refl } }
end

end localization

/-- This awful function produces r1.s as a unit in localization r2 -/
noncomputable def s_inv_aux (r1 r2 : rational_open_data A) (h : r1 ≤ r2) :
  units (localization r2) :=
@units.unit_of_mul_left_eq_unit _ _
  ((of_id A (localization r2) : A → r2.localization) r1.s)
  ((of_id A (localization r2) : A → r2.localization) (classical.some h))
  (localization.to_units (⟨r2.s, 1, by simp⟩ : powers r2.s))
  begin
    rw [← alg_hom.map_mul, (classical.some_spec h).1],
    refl,
  end

/-- The map A(T1/s1) -> A(T2/s2) coming from the inequality r1 ≤ r2 -/
noncomputable def localization_map {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
  localization r1 → localization r2 :=
Huber_ring.away.lift r1.T r1.s
( show ((s_inv_aux r1 r2 h)⁻¹).inv = (of_id A (localization r2)).to_fun r1.s, from rfl)

instance {r1 r2 : rational_open_data A} (h : r1 ≤ r2) : is_ring_hom
(localization_map h) := by delta localization_map; apply_instance

-- To prove continuity of the localisation map coming from r1 ≤ r2 I need to check
-- that the image of T/s in the r1 ring is power-bounded in the r2 ring. This is
-- this lemma.

local attribute [instance] set.pointwise_mul_comm_semiring
local attribute [instance] set.pointwise_mul_action

lemma localization_map_is_cts_aux {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
is_power_bounded_subset
  ((s_inv_aux r1 r2 h)⁻¹.val • (λ (x : ↥A), to_fun (localization r2) x) '' r1.T) :=
begin
  refine power_bounded.subset _ (localization.power_bounded r2),
  intros x hx,
  rcases hx with ⟨y, hy, hz, ⟨t₁, ht₁, rfl⟩, rfl⟩,
  rw set.mem_singleton_iff at hy, rw hy, clear hy, clear y,
  let h' := h, -- need it later
  rcases h with ⟨a, ha, h₂⟩,
  rcases h₂ t₁ ht₁ with ⟨t₂, ht₂, N, hN⟩,
  show ↑(s_inv_aux r1 r2 _)⁻¹ * to_fun (localization r2) t₁ ∈
    localization.mk 1 ⟨r2.s, _⟩ • (of_id ↥A (localization r2)).to_fun '' r2.T,
  rw set.mem_smul_set,
  use (of_id ↥A (localization r2)).to_fun t₂,
  existsi _, swap,
    rw set.mem_image, use t₂, use ht₂,
  rw [←units.mul_left_inj (s_inv_aux r1 r2 h'), units.mul_inv_cancel_left],
  show to_fun (localization r2) t₁ = to_fun (localization r2) (r1.s) *
    (localization.mk 1 ⟨r2.s, _⟩ * to_fun (localization r2) t₂),
  rw [mul_comm, mul_assoc],
  rw ←units.mul_left_inj (localization.to_units (⟨r2.s, 1, by simp⟩ : powers r2.s)),
  rw ←mul_assoc,
  -- t1=s1*(1/s2 * t2) in r2
  have : ↑(localization.to_units (⟨r2.s, 1, by simp⟩ : powers r2.s)) *
    localization.mk (1 : A) (⟨r2.s, 1, by simp⟩ : powers r2.s) = 1,
  convert units.mul_inv _,
  rw [this, one_mul], clear this,
  show to_fun (localization r2) r2.s * _ = _,
  rw ←units.mul_left_inj (localization.to_units (⟨r2.s ^ N, N, rfl⟩ : powers r2.s)),
  show to_fun (localization r2) (r2.s ^ N) * _ = to_fun (localization r2) (r2.s ^ N) * _,
  have hrh : is_ring_hom (to_fun (localization r2)) := begin
    change is_ring_hom ((of_id ↥A (localization r2)).to_fun),
    apply_instance,
  end,
  rw ←@is_ring_hom.map_mul _ _ _ _ (to_fun (localization r2)) hrh,
  rw ←@is_ring_hom.map_mul _ _ _ _ (to_fun (localization r2)) hrh,
  rw ←@is_ring_hom.map_mul _ _ _ _ (to_fun (localization r2)) hrh,
  rw ←@is_ring_hom.map_mul _ _ _ _ (to_fun (localization r2)) hrh,
  congr' 1,
  rw [←mul_assoc _ t₂, hN],
  rw ←ha, ring,
end

-- Continuity now follows from the universal property.
lemma localization_map_is_cts {r1 r2 : rational_open_data A} (h : r1 ≤ r2) :
  continuous (localization_map h) := Huber_ring.away.lift_continuous r1.T r1.s
  (localization.nonarchimedean r2) (Huber_ring.away.of_continuous r2.T r2.s _) _ _
  (localization_map_is_cts_aux h)

end rational_open_data -- namespace

end spa

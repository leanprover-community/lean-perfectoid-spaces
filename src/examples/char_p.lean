import ring_theory.power_series
import algebra.char_p algebra.group_power

import for_mathlib.nnreal
import for_mathlib.char_p

import valuation.perfection
import perfectoid_space

noncomputable theory
open_locale classical
open function

local postfix `ᵒ` : 66 := power_bounded_subring

local attribute [instance] nnreal.pow_enat

namespace power_series
variables (K : Type*) [discrete_field K]

def valuation (b : {r : nnreal // 0 < r ∧ r < 1}) : valuation (power_series K) nnreal :=
{ to_fun := λ φ, b ^ φ.order,
  map_zero' := by rw [order_zero, nnreal.pow_enat_top],
  map_one' := by rw [order_one, nnreal.pow_enat_zero],
  map_mul' := λ x y, by rw [order_mul, nnreal.pow_enat_add],
  map_add' := λ x y,
  begin
    have : _ ≤ _ := order_add_ge x y,
    rw min_le_iff at this,
    rw le_max_iff,
    have b_ne_zero : (b : nnreal) ≠ 0 := ne_of_gt b.2.left,
    cases this with h h; [left, right],
    all_goals
    { apply nnreal.pow_enat_le _ b_ne_zero _ _ _ h,
      exact le_of_lt b.2.right, },
  end }

end power_series

/- The following definition is mathematically correct,
but probably not the version that we want to put into mathlib.
We make it for the sole purpose of constructing a perfectoid field.-/
def laurent_series (K : Type*) [discrete_field K] := localization.fraction_ring (power_series K)

namespace laurent_series
variables (p : nat.primes) (K : Type*) [discrete_field K]

instance : discrete_field (laurent_series K) := by delta laurent_series; apply_instance

def algebra : algebra K (laurent_series K) :=
algebra.of_ring_hom (localization.of ∘ power_series.C K) $
@is_ring_hom.comp _ _ _ _ (power_series.C K) (ring_hom.is_ring_hom _)
  _ _ localization.of localization.of.is_ring_hom

variables [char_p K p]

def valuation (b : {r : nnreal // 0 < r ∧ r < 1}) : valuation (laurent_series K) nnreal :=
valuation.localization (power_series.valuation K b) $ λ φ h,
begin
  rw localization.fraction_ring.mem_non_zero_divisors_iff_ne_zero at h,
  contrapose! h,
  change (_ : nnreal) ^ φ.order = 0 at h,
  have b_ne_zero : (b : nnreal) ≠ 0 := ne_of_gt b.2.left,
  rw ← power_series.order_eq_top,
  apply (nnreal.pow_enat_inj _ b_ne_zero b.2.right),
  rwa nnreal.pow_enat_top,
end

lemma non_trivial (b : {r : nnreal // 0 < r ∧ r < 1}) : ¬ (valuation K b).is_trivial :=
begin
  have b_ne_zero : (b : nnreal) ≠ 0 := ne_of_gt b.2.left,
  assume H, cases H (localization.of (power_series.X)) with h h;
  erw valuation.localization_apply at h; change _ ^ _ = _ at h,
  { apply b_ne_zero,
    simpa only [nnreal.pow_enat_one, power_series.order_X] using h },
  { simp only [nnreal.pow_enat_one, power_series.order_X] at h,
    exact ne_of_lt b.2.right h, },
end

local attribute [instance] algebra

instance [char_p K p] : char_p (laurent_series K) p :=
char_p_algebra_over_field K

end laurent_series

def laurent_series_perfection (K : Type*) [discrete_field K] :=
perfect_closure (laurent_series K) (ring_char K)

namespace laurent_series_perfection
variables (p : nat.primes) (K : Type*) [discrete_field K] [hp : char_p K p]
include hp

instance : discrete_field (laurent_series_perfection K) :=
@perfect_closure.discrete_field (laurent_series K) _ _ (ring_char.prime p K) $
by { rw ← ring_char.eq K hp, apply_instance }

def valuation (b : {r : nnreal // 0 < r ∧ r < 1}) :
  valuation (laurent_series_perfection K) nnreal :=
@valuation.perfection (laurent_series K) _ (laurent_series.valuation K b)
(ring_char K) (ring_char.prime p _) $
by { rw ← ring_char.eq K hp, apply_instance }

lemma non_discrete (b : {r : nnreal // 0 < r ∧ r < 1}) (ε : nnreal) (h : 0 < ε) :
  ∃ x : laurent_series_perfection K, 1 < valuation p K b x ∧ valuation p K b x < 1 + ε :=
@valuation.perfection.non_discrete _ _ _ (ring_char.prime p _)
(by { rw ← ring_char.eq K hp, apply_instance }) _ (laurent_series.non_trivial K b) ε h

lemma non_trivial (b : {r : nnreal // 0 < r ∧ r < 1}) : ¬ (valuation p K b).is_trivial :=
begin
  rcases non_discrete p K b 2 (by norm_num) with ⟨x, h₁, h₂⟩,
  contrapose! h₁, cases h₁ x with h h; rw h,
  exact zero_le _,
end

lemma frobenius_surjective : surjective (frobenius (laurent_series_perfection K) p) :=
begin
  rw ring_char.eq K hp,
  let F := (perfect_closure.frobenius_equiv (laurent_series K) _),
  { exact F.surjective },
  { exact ring_char.prime p K },
  { rw ← ring_char.eq K hp, apply_instance }
end

def algebra : algebra (laurent_series K) (laurent_series_perfection K) :=
algebra.of_ring_hom (perfect_closure.of _ _) $
@perfect_closure.is_ring_hom _ _ _ (ring_char.prime _ _) $
by { rw ← ring_char.eq K hp, apply_instance }

end laurent_series_perfection

namespace laurent_series_perfection
-- Now we take K in universe Type. For example `valued` requires this.
variables (p : nat.primes) (K : Type) [discrete_field K] [char_p K p]
include p

protected def valued (b : {r : nnreal // 0 < r ∧ r < 1}) : valued (laurent_series_perfection K) :=
{ Γ₀ := nnreal, v := valuation p K b }

def valued_p : valued (laurent_series_perfection K) :=
laurent_series_perfection.valued p K ⟨p⁻¹,
begin
  have p_inv_ne_zero : (p⁻¹ : nnreal) ≠ 0,
  { assume H, apply p.ne_zero,
    rw [← inv_inj'', inv_zero', inv_inv'', eq_comm, (show (p:nnreal) = (p:ℕ), by rw coe_coe)] at H,
    exact_mod_cast H.symm, },
  split,
  { exact lt_of_le_of_ne (zero_le _) p_inv_ne_zero.symm, },
  { rw [← linear_ordered_structure.inv_lt_inv, inv_one', inv_inv'',
        (show (p:nnreal) = (p:ℕ), by rw coe_coe)],
    { exact_mod_cast p.one_lt },
    { exact one_ne_zero },
    { exact p_inv_ne_zero } }
end⟩

end laurent_series_perfection

namespace valuation
variables {R : Type*} [comm_ring R]
variables {Γ₀ : Type*} [linear_ordered_comm_group_with_zero Γ₀]

local attribute [instance] classical.decidable_linear_order

def le_one_subring (v : valuation R Γ₀) := {r : R | v r ≤ 1}

instance le_one_subring.is_subring (v : valuation R Γ₀) : is_subring v.le_one_subring :=
-- @subtype.comm_ring R _ {r : R | v r ≤ 1}
{ zero_mem := show v 0 ≤ 1, by simp,
  one_mem := show v 1 ≤ 1, by simp,
  add_mem := λ r s (hr : v r ≤ 1) (hs : v s ≤ 1), show v (r+s) ≤ 1,
  by calc v (r + s) ≤ max (v r) (v s) : v.map_add r s
                ... ≤ 1 : max_le hr hs,
  neg_mem := λ r (hr : v r ≤ 1), show v (-r) ≤ 1, by rwa [v.map_neg],
  mul_mem := λ r s (hr : v r ≤ 1) (hs : v s ≤ 1), show v (r*s) ≤ 1,
  begin
    rw v.map_mul,
    refine le_trans (actual_ordered_comm_monoid.mul_le_mul_right' hr) _,
    rwa one_mul
  end }

instance coe_nat_le_one_subring (v : valuation R Γ₀) :
  has_coe ℕ v.le_one_subring := by apply_instance

end valuation

section pfd_fld
parameter (p : nat.primes)
variables (K : Type)

-- class perfectoid_field : Type 1 :=
-- [fld : discrete_field K]
-- [top : uniform_space K]
-- [top_fld : topological_division_ring K]
-- [complete : complete_space K]
-- [sep : separated K]
-- (v : valuation K nnreal)
-- (non_discrete : ∀ ε : nnreal, 0 < ε → ∃ x : K, 1 < v x ∧ v x < 1 + ε)
-- (Frobenius : surjective (Frob v.le_one_subring ∕p))

end pfd_fld

section
open uniform_space
variables (p : nat.primes) (K : Type) [discrete_field K] [char_p K p]
include p

local attribute [instance] valued.subgroups_basis subgroups_basis.topology
  ring_filter_basis.topological_ring valued.uniform_space laurent_series_perfection.valued_p

/-- The completion of the perfection of the Laurent series over a field. -/
def clsp := completion (laurent_series_perfection K)

end

section char_p_completion
open uniform_space
variables {R : Type*} [comm_ring R] [uniform_space R] [uniform_add_group R] [separated R]
  [topological_ring R] (p : nat.primes) [char_p R p]

instance completion.char_p : char_p (completion R) p :=
(subring_char_p p (completion.uniform_embedding_coe R).inj).mpr ‹_›

end char_p_completion

section
open uniform_space
--variables (K : Type*) [discrete_field K] [topological_space K] [topological_division_ring K]
variables {G : Type*} [add_comm_group G] [uniform_space G] [uniform_add_group G]
variables {H : Type*} [add_comm_group H] [uniform_space H] [uniform_add_group H]
variables {φ : G → H} {ψ : H → G} (h : φ ∘ ψ = id) [is_add_group_hom φ] [is_add_group_hom ψ]
  (hφ : continuous φ) (hψ : continuous ψ)
include h hφ hψ
local notation `hat` x:90 := completion.map x

lemma johan : surjective hat φ :=
have key : hat φ ∘ hat ψ = id,
  by { rw [← completion.map_id, ← h],
       exact completion.map_comp (uniform_continuous_of_continuous hφ)
                              (uniform_continuous_of_continuous hψ) },
λ y, ⟨(hat ψ) y, congr_fun key _⟩
end

namespace uniform_space.completion
open uniform_space
variables {α : Type*} [ring α] [uniform_space α] [topological_ring α] [uniform_add_group α]

local infix `^` := monoid.pow

@[move_cast]
lemma coe_pow (a : α) (n : ℕ): ((a^n : α) : completion α) = a^n :=
begin
  induction n with n ih,
  exact completion.coe_one _,
  change ↑(a*a^n) = ↑a*↑a^n,
  rw [coe_mul, ih],
end
end uniform_space.completion

section
open uniform_space
variables (p : nat.primes) (K : Type) [discrete_field K] [char_p K p] [uniform_space K]
  [uniform_add_group K] [topological_division_ring K] [separated K]

lemma completion.frobenius_eq : frobenius (completion K) p = completion.map (frobenius K p) :=
begin
  symmetry,
  apply completion.map_unique,
  { haveI hom : is_ring_hom (frobenius (completion K) p) := by {
    apply frobenius.is_ring_hom _,
    exact p.property,
    exact completion.char_p _,
  },
    haveI : topological_monoid (completion K) := topological_ring.to_topological_monoid _,
    exact uniform_continuous_of_continuous (continuous_pow p)
    },
  { intro x,
    simp [frobenius],
    erw completion.coe_pow,
    refl }
end
end

namespace clsp
open uniform_space
variables (p : nat.primes) (K : Type) [discrete_field K] [char_p K p]
include p

local attribute [instance] valued.subgroups_basis subgroups_basis.topology
  ring_filter_basis.topological_ring valued.uniform_space valued.uniform_add_group
  laurent_series_perfection.valued_p

instance : discrete_field (clsp p K) := completion.discrete_field
instance : uniform_space (clsp p K) := completion.uniform_space _
instance : topological_division_ring (clsp p K) := completion.topological_division_ring
instance : complete_space (clsp p K) := completion.complete_space _
instance : separated (clsp p K) := completion.separated _

def valuation : valuation (clsp p K) nnreal := valued.extension_valuation

lemma frobenius_surjective : surjective (frobenius (clsp p K) p) :=
begin
  dsimp [clsp],
  set lsp := (laurent_series_perfection K),
  haveI char : char_p lsp ↑p := sorry,
  rw completion.frobenius_eq,
  obtain ⟨ψ, inv, cont⟩ : ∃ ψ : (laurent_series_perfection K) → (laurent_series_perfection K),
    (frobenius lsp p) ∘ ψ = id ∧ continuous ψ,
  {
    sorry },

  sorry
end

-- instance laurent_series_valued : valued (laurent_series K) :=
-- { Γ₀ := nnreal, v := laurent_series.valuation p K }

-- protected def algebra : algebra (laurent_series_perfection K) (clsp p K) :=
-- algebra.of_ring_hom
--   (coe : (laurent_series_perfection K) → completion (laurent_series_perfection K)) $
-- @completion.is_ring_hom_coe (laurent_series_perfection K) _ _ _ $
-- @valued.uniform_add_group (laurent_series_perfection K) _ $ laurent_series_perfection.valued p K

-- def rod_algebra : algebra (power_series K) (clsp p K) :=
-- @algebra.comap.algebra _ _ _ _ _ _ _ $
-- @algebra.comap.algebra (laurent_series K) (laurent_series_perfection K) (clsp p K) _ _ _
-- (laurent_series_perfection.algebra p K) (clsp.algebra p K)

-- def rod : Huber_ring.ring_of_definition (laurent_series K) (clsp p K) :=
-- {
--   .. rod_algebra p K }

-- def Huber_ring : Huber_ring (clsp p K) :=
-- { pod :=
--   begin
--   end }

-- instance : perfectoid_field p (clsp p K) :=
-- { v := valuation p K,
--   non_discrete := λ ε h,
--   begin
--     choose x hx using laurent_series_perfection.non_discrete p K ε h,
--     delta clsp, use x,
--     convert hx using 2; exact valued.extension_extends _
--   end,
--   Frobenius :=
--   begin
--     apply @surjective.of_comp _ _ _ _ (ideal.quotient.mk _) _,
--     conv {congr, simp only [frobenius, comp], funext, rw [← ideal.quotient.mk_pow]},
--     apply surjective_comp,
--     { rintro ⟨x⟩, exact ⟨x, rfl⟩ },
--     intro x,
--     choose y hy using frobenius_surjective p K x.val,
--     have hvy : valuation p K y ≤ 1,
--     { have aux := congr_arg (valuation p K) hy,
--       replace hy := x.property,
--       rw [← aux, frobenius, valuation.map_pow] at hy, clear aux,
--       apply linear_ordered_structure.le_one_of_pow_le_one _ _ hy,
--       exact_mod_cast p.ne_zero, },
--     refine ⟨⟨y, hvy⟩, _⟩,
--     { rw [subtype.ext], convert hy,
--       convert @is_semiring_hom.map_pow _ _ _ _ subtype.val _ ⟨y,_⟩ p,
--        }
--   end }

end clsp

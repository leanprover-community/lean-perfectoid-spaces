import ring_theory.localization
universes u v

namespace localization
-- line 170

/-
@[simp] lemma mk_zero {x : α} {hx : x ∈ S} :
  (mk 0 ⟨x, hx⟩ : localization α S) = 0 :=
quotient.sound ⟨1, is_submonoid.one_mem S, by simp⟩


-/

theorem localization.mk_zero {α : Type u} [comm_ring α] {S : set α}
  [is_submonoid S] {x : α} {hx : x ∈ S} :
  mk 0 ⟨x, hx⟩ = 0 := quotient.sound ⟨1, is_submonoid.one_mem S, by simp⟩

end localization

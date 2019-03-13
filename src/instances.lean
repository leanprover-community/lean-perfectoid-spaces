import data.padics

import for_mathlib.padics

import Huber_ring

/-
jmc: The first goal of this file is to show that the p-adics form a Huber ring.
jmc: We may extend this with other examples later.
-/

noncomputable instance padic.Huber_ring (p : ℕ) [p.prime] :
  Huber_ring ℚ_[p] :=
{ pod := ⟨ℤ_[p], infer_instance, infer_instance, padic_int.topological_ring,
  ⟨{ f   := (λ x : ℤ_[p], x),
     hom := padic_int.coe_is_ring_hom,
     emb := embedding_subtype_val,
     hf  := sorry,
     J   := nonunits_ideal padic_int.is_local_ring,
     fin := ⟨{p}, ⟨set.finite_singleton _, padic_int.nonunits_ideal_eq.symm⟩⟩,
     top := sorry }⟩⟩ }

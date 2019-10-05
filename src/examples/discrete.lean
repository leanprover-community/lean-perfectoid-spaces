import Huber_ring.basic

local attribute [instance] discrete_top_ring

/-- Chambert-Loir's lemma: a discrete ring is Huber. -/
lemma discrete_Huber_ring {A : Type*} [comm_ring A] [topological_space A] [discrete_topology A] :
  Huber_ring A :=
⟨⟨A, by assumption, by assumption, by apply_instance,
           ⟨{ emb := open_embedding_id,
              J := ⊥,
              fin := submodule.fg_bot,
              top := is_bot_adic_iff.mpr ‹_›,
              .. algebra.id A }⟩⟩⟩

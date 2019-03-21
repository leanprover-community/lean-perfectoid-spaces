import data.finset

local attribute [instance] classical.prop_decidable

namespace finset
open function
variables {α : Type*} {β : Type*} (t : finset β) (f : α → β)

set_option pp.proofs true

lemma exists_finset_of_surjective (h : surjective f) :
  ∃ (s : finset α), s.image f = t :=
⟨t.bind $ λ b, singleton $ classical.some $ h b,
begin
  ext b,
  simp only [bind_image, mem_bind, mem_image],
  split; intro H,
  { rcases H with ⟨b', hb', a, ha, H⟩,
    erw [mem_singleton] at ha,
    subst ha,
    subst H,
    rwa classical.some_spec (h b') },
  { use [b, H],
    refine ⟨_, mem_singleton_self _, _⟩,
    rw classical.some_spec (h b) }
end⟩

lemma exists_finset_of_subset_range (h : (↑t : set β) ⊆ set.range f) :
  ∃ (s : finset α), s.image f = t :=
begin
  let f' := set.range_factorization f,
  let t' : finset (set.range f) := finset.subtype _ t,
  cases exists_finset_of_surjective t' f' (set.surjective_onto_range) with s hs,
  use s,
  convert congr_arg (image subtype.val) hs,
  { erw [image_image, set.range_factorization_eq] },
  { ext b,
    erw mem_image,
    split; intro H,
    { refine ⟨⟨b, h H⟩, mem_subtype.mpr H, rfl⟩ },
    { rcases H with ⟨_, _, rfl⟩,
      exact mem_subtype.mp ‹_› } }
end

lemma exists_finset_of_subset_image (s : set α) (h : (↑t : set β) ⊆ f '' s) :
  ∃ (s' : finset α), s'.image f = t ∧ (↑s' : set α) ⊆ s :=
begin
  have H : ↑t ⊆ set.range (f ∘ (subtype.val : s → α)) :=
    by rw [set.range_comp, set.subtype.val_range]; exact h,
  cases exists_finset_of_subset_range t (f ∘ (subtype.val : s → α)) H with s' hs',
  refine ⟨(s'.image (subtype.val : s → α)), _, _⟩,
  { erw image_image, exact hs' },
  { erw coe_image,
    apply subtype.val_image_subset }
end

end finset

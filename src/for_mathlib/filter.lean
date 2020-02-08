import order.filter.basic

import for_mathlib.data.set.basic

local infixr ` ×ᶠ `:51 := filter.prod

section
open filter set function

lemma filter.comap_pure {α : Type*} {β : Type*} {f : α → β} (h : injective f) (a : α) :
  pure a = comap f (pure $ f a) :=
by rw [← filter.map_pure, comap_map h]

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

/-
    f
  α → β
g ↓   ↓ h
  γ → δ
    i
-/
variables {f : α → β} {g : α → γ} {h : β → δ} {i : γ → δ} (H : h ∘ f = i ∘ g)
include H

lemma filter.map_comm (F : filter α) : map h (map f F) = map i (map g F) :=
by rw [filter.map_map, H, ← filter.map_map]

lemma filter.comap_comm (G : filter δ) : comap f (comap h G) = comap g (comap i G) :=
by rw [filter.comap_comap_comp, H, ← filter.comap_comap_comp]
omit H


open lattice
variables {G : filter β} {s : set α} {t : set β} {φ : α → β}

lemma mem_comap_sets_of_inj (h : ∀ a a', φ a = φ a' → a = a') :
  s ∈ comap φ G ↔ ∃ t ∈ G, s = φ ⁻¹' t :=
begin
  rw mem_comap_sets,
  split ; rintros ⟨t, ht, hts⟩,
  { use t ∪ φ '' s,
    split,
    { simp [mem_sets_of_superset ht] },
    { rw [preimage_union, preimage_image_eq _ h],
      exact (union_eq_self_of_subset_left hts).symm } },
  { use [t, ht],
    rwa hts }
end

lemma filter.inf_eq_bot_iff {α : Type*} (f g : filter α) : f ⊓ g = ⊥ ↔ ∃ (U ∈ f) (V ∈ g), U ∩ V = ∅ :=
by { rw [← empty_in_sets_eq_bot, mem_inf_sets], simp [subset_empty_iff] }

lemma filter.ne_bot_of_map {α : Type*} {β : Type*} {f : α → β} {F : filter α} (h : map f F ≠ ⊥) : F ≠ ⊥ :=
λ H, (H ▸ h : map f ⊥ ≠ ⊥) map_bot

lemma filter.map_prod_prod {α₁ : Type*} {α₂ : Type*} {β₁ : Type*} {β₂ : Type*}
  (f : α₁ → α₂) (g : β₁ → β₂) (F : filter α₁) (G : filter β₁) :
  map (f ⨯ g) (F ×ᶠ G) = (map f F) ×ᶠ (map g G) :=
by { rw filter.prod_map_map_eq, refl }

lemma filter.map_prod_mk {α : Type*} {β : Type*} {γ : Type*} (f : γ → α) (g : γ → β) (F : filter γ) :
  map (λ x, prod.mk (f x) $ g x) F ≤ (map f F).prod (map g F) :=
begin
  intros U U_in,
  rcases mem_prod_iff.1 U_in with ⟨s, s_in, t, t_in, stU⟩,
  rw mem_map at *,
  have st_in := filter.inter_sets F s_in t_in,
  apply mem_sets_of_superset st_in,
  rintro x ⟨xs, xt⟩,
  apply stU,
  exact ⟨xs, xt⟩
end
end


class filter_basis (α : Type*) :=
(sets : set $ set α)
(ne_empty : sets.nonempty) -- avoid the degenerate case of an empty filter basis
(directed : ∀ {s t}, s ∈ sets → t ∈ sets → ∃ u ∈ sets, u ⊆ s ∩ t)

namespace filter_basis
open filter set function

variables {α : Type*} {ι : Type*} (B : filter_basis α)

--instance : has_coe (filter_basis α) (set $ set α) := ⟨filter_basis.sets α⟩
instance : has_mem (set α) (filter_basis α) := ⟨λ s B, s ∈ B.sets⟩

lemma mem_iff {B : filter_basis α} {s : set α} : s ∈ B ↔ s ∈ B.sets := iff.rfl

def default (B : filter_basis α) : set α :=
B.ne_empty.some

def default_in (B : filter_basis α) : B.default ∈ B :=
B.ne_empty.some_mem

def filter : filter α := generate B.sets

lemma mem_filter {U : set α} : U ∈ B.filter ↔ ∃ V ∈ B, V ⊆ U :=
begin
  split ; intro h,
  { induction h with U U_in U V U_gen UV U_union U V U_gen V_gen U_union V_union,
    { exact ⟨U, U_in, le_refl U⟩ },
    { exact ⟨B.default, B.default_in, subset_univ _⟩ },
    { rcases U_union with ⟨W, W_in, WU⟩,
      refine ⟨W, W_in, subset.trans WU UV⟩ },
    { rcases U_union with ⟨S, S_in, SU⟩,
      rcases V_union with ⟨T, T_in, TU⟩,
      rcases filter_basis.directed S_in T_in with ⟨W, W_in, hW⟩,
      cases subset_inter_iff.1 hW with WS WT,
      exact ⟨W, W_in, subset_inter_iff.2 ⟨subset.trans WS SU, subset.trans WT TU⟩⟩ } },
  { rcases h with ⟨V, V_in, VU⟩,
    exact generate_sets.superset (generate_sets.basic $ V_in) VU },
end

lemma mem_filter_of_mem {B : filter_basis α} {U : set α} (h : U ∈ B) : U ∈ B.filter :=
generate_sets.basic h

lemma le_filter (F : _root_.filter α) : F ≤ B.filter ↔ ∀ U ∈ B, U ∈ F :=
begin
  split ; intros h U U_in,
  { exact h (mem_filter_of_mem U_in) },
  { rcases B.mem_filter.1 U_in with ⟨V, V_in, VU⟩,
    filter_upwards [h V V_in],
    exact VU },
end

lemma filter_le (F : _root_.filter α) : B.filter ≤ F ↔ ∀ {V}, V ∈ F → ∃ U ∈ B, U ⊆ V :=
begin
  simp only [B.mem_filter],
  split ; intros h V V_in,
  { exact B.mem_filter.1 (h V_in) },
  { exact B.mem_filter.2 (h V_in) },
end


def map {β : Type*} (f : α → β) (B : filter_basis α) : filter_basis β :=
{ sets := (image f) '' B.sets,
  ne_empty := image_nonempty _ _ B.ne_empty,
  directed := begin
    rintros _ _ ⟨U, U_in, rfl⟩ ⟨V, V_in, rfl⟩,
    rcases filter_basis.directed U_in V_in with ⟨W, W_in, UVW⟩,
    use [f '' W, mem_image_of_mem _ W_in],
    exact subset.trans (image_subset f UVW) (image_inter_subset f U V)
  end }

lemma mem_map {β : Type*} (f : α → β) (B : filter_basis α) {V : set β} :
  V ∈ map f B ↔ ∃ U ∈ B, f '' U = V :=
begin
  change V ∈ image f '' B.sets ↔ ∃ (U : set α) (H : U ∈ B), f '' U = V,
  simp [mem_image],
  exact iff.rfl,
end

def map_filter {β : Type*} (f : α → β) (B : filter_basis α) :
  filter.map f B.filter = (map f B).filter :=
begin
  ext V,
  simp [filter.mem_map, mem_filter, mem_filter, mem_map],
  split,
  { rintros ⟨U, UB, H⟩,
    use [f '' U, U, UB],
    exact image_subset_iff.2 H },
  { rintros ⟨W, ⟨U, UB, rfl⟩, H⟩,
    use [U, UB],
    exact image_subset_iff.1 H },
end

lemma tendsto_from {β : Type*} (f : α → β) (F : _root_.filter β) :
  tendsto f B.filter F ↔ ∀ {V}, V ∈ F → ∃ U ∈ B, U ⊆ f ⁻¹' V :=
begin
  apply forall_congr,
  intros V,
  apply imp_congr iff.rfl,
  rw [filter.mem_map, mem_filter],
  exact iff.rfl
end

lemma tendsto_into {β : Type*} (f : β → α) (F : _root_.filter β) :
  tendsto f F B.filter ↔ ∀ {V}, V ∈ B → f ⁻¹' V ∈ F :=
begin
  split ; intros h U U_in,
  { exact h (mem_filter_of_mem U_in) },
  { rcases B.mem_filter.1 U_in with ⟨V, V_in, H⟩,
    filter_upwards [h V_in],
    exact preimage_mono H },
end

lemma tendsto_both {β : Type*} (f : α → β) (B' : filter_basis β) :
  tendsto f B.filter B'.filter ↔ ∀ {V}, V ∈ B' → ∃ U ∈ B, U ⊆ f ⁻¹' V :=
begin
  rw tendsto_into,
  apply forall_congr,
  intros V,
  exact imp_congr iff.rfl (mem_filter _)
end

universes u v

protected def prod {α : Type u} {β : Type v} (B : filter_basis α) (B' : filter_basis β) :
  filter_basis (α × β) :=
{ sets :=  (uncurry' set.prod) '' (B.sets.prod B'.sets),
  ne_empty := image_nonempty _ _ (set.prod_nonempty_iff.2 ⟨B.ne_empty, B'.ne_empty⟩),
  directed := begin
    rintros _ _ ⟨⟨P, P'⟩, ⟨P_in, P_in'⟩, rfl⟩ ⟨⟨Q, Q'⟩, ⟨Q_in, Q_in'⟩, rfl⟩,
    rcases filter_basis.directed P_in Q_in with ⟨U, U_in, hU⟩,
    rcases filter_basis.directed P_in' Q_in' with ⟨U', U_in', hU'⟩,
    use set.prod U U',
    simp only [uncurry', exists_prop],
    use [(U, U'), ⟨U_in, U_in'⟩],
    rintros ⟨x, y⟩ ⟨x_in, y_in⟩,
    cases hU x_in,
    cases hU' y_in,
    finish
  end }

lemma mem_prod_of_mem {α : Type u} {β : Type v} {B : filter_basis α} {B' : filter_basis β}
  {S} (hS : S ∈ B) {T} (hT : T ∈ B') : set.prod S T ∈ B.prod B' :=
⟨(S, T), mem_prod.2 ⟨hS, hT⟩, rfl⟩

lemma mem_prod_filter_of_mem {α : Type u} {β : Type v} {B : filter_basis α} {B' : filter_basis β}
  {S} (hS : S ∈ B) {T} (hT : T ∈ B') : set.prod S T ∈ (B.prod B').filter :=
mem_filter_of_mem (mem_prod_of_mem hS hT)

lemma mem_prod_filter {α : Type u} {β : Type v} (B : filter_basis α) (B' : filter_basis β)
  {U : set (α × β)} : U ∈ (B.prod B').filter ↔ ∃ S ∈ B, ∃ T ∈ B', set.prod S T ⊆ U :=
begin
  rw mem_filter,
  split,
  { rintros ⟨_, ⟨⟨S, T⟩, h, rfl⟩, H⟩,
    exact ⟨S, h.1, T, h.2, H⟩ },
  { rintros ⟨S, S_in, T, T_in, H⟩,
    exact ⟨set.prod S T, mem_prod_of_mem S_in T_in, H⟩ }
end

lemma prod_filter {α : Type u} {β : Type v} (B : filter_basis α) (B' : filter_basis β) :
(B.prod B').filter = B.filter ×ᶠ B'.filter :=
begin
  ext U,
  rw [mem_prod_filter, filter.mem_prod_iff],
  split ; rintros ⟨S, ⟨Sin, T, Tin, H⟩⟩,
  { exact ⟨S, mem_filter_of_mem Sin, T, mem_filter_of_mem Tin, H⟩ },
  { rcases B.mem_filter.1 Sin with ⟨V, Vin, VS⟩,
    rcases B'.mem_filter.1 Tin with ⟨W, Win, WT⟩,
    use [V, Vin, W, Win],
    exact subset.trans (set.prod_mono VS WT) H }
end
end filter_basis

import topology.opens

import for_mathlib.filter
import for_mathlib.data.set.basic

open topological_space function

local notation `𝓝` x:70 := nhds x
local notation f `∘₂` g := function.bicompr f g

-- We need to think whether we could directly use the class t2_space (which is not using opens though)
definition is_hausdorff (α : Type*) [topological_space α] : Prop :=
  ∀ x y, x ≠ y → ∃ u v : opens α, x ∈ u ∧ y ∈ v ∧ u ∩ v = ∅

open set filter

instance regular_of_discrete {α : Type*} [topological_space α] [discrete_topology α] :
  regular_space α :=
{ t1 := λ x, is_open_discrete _,
  regular :=
  begin
    intros s a s_closed a_not,
    refine ⟨s, is_open_discrete s, subset.refl s, _⟩,
    erw [← empty_in_sets_eq_bot, mem_inf_sets],
    use {a},
    rw nhds_discrete α,
    simp,
    refine ⟨s, subset.refl s, _ ⟩,
    rintro x ⟨xa, xs⟩,
    rw ← mem_singleton_iff.1 xa at a_not,
    exact a_not xs
  end }


lemma continuous_of_const {α : Type*} {β : Type*}
  [topological_space α] [topological_space β]
  {f : α → β} (h : ∀a b, f a = f b) :
  continuous f :=
λ s _, by convert @is_open_const _ _ (∃ a, f a ∈ s); exact
  set.ext (λ a, ⟨λ fa, ⟨_, fa⟩,
    λ ⟨b, fb⟩, show f a ∈ s, from h b a ▸ fb⟩)

section
variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}

variables [topological_space α] [topological_space β] [topological_space γ] [topological_space δ]

def continuous₂ (f : α → β → γ) := continuous (function.uncurry' f)

lemma continuous₂_def (f : α → β → γ) : continuous₂ f ↔ continuous (function.uncurry' f) := iff.rfl

lemma continuous₂_curry (f : α × β → γ) : continuous₂ (function.curry f) ↔ continuous f :=
by rw  [←function.uncurry'_curry f] {occs := occurrences.pos [2]} ; refl

lemma continuous₂.comp {f : α → β → γ} {g : γ → δ} (hf : continuous₂ f)(hg : continuous g) :
  continuous₂ (g ∘₂ f) := hg.comp hf

section
open set filter lattice function

/-
    f
  α → β
g ↓   ↓ h
  γ → δ
    i
-/
variables {f : α → β} {g : α → γ} {i : γ → δ} {h : β → δ}

lemma continuous_of_continuous_on_of_induced (H : h ∘ f = i ∘ g) (hi : continuous_on i $ range g)
  (hg : ‹topological_space α› = induced g ‹topological_space γ›)
  (hh : ‹topological_space β› = induced h ‹topological_space δ›) : continuous f :=
begin
  rw continuous_iff_continuous_at,
  intro x,
  dsimp [continuous_at, tendsto],
  rw [hg, hh, nhds_induced, nhds_induced, ← map_le_iff_le_comap, map_comm H],
  specialize hi (g x) ⟨x, rfl⟩,
  have := calc
    nhds_within (g x) (range g) = 𝓝 g x ⊓ principal (range g) : rfl
    ... = 𝓝 g x ⊓ map g (principal univ) : by rw [← image_univ, ← map_principal]
    ... = 𝓝 g x ⊓ map g ⊤ : by rw principal_univ,
  rw [continuous_within_at, this, ← comp_app i g, ← congr_fun H x] at hi, clear this,
  have := calc
    map g (comap g 𝓝 g x) = map g (comap  g 𝓝 g x ⊓ ⊤) : by rw inf_top_eq
    ... ≤ map g (comap g 𝓝 g x) ⊓ map g ⊤ : map_inf_le g _ _
    ... ≤ 𝓝 g x ⊓ map g ⊤ : inf_le_inf map_comap_le (le_refl _),
  exact le_trans (map_mono this) hi,
end

variables  (eg : embedding g) (eh : embedding h)
include eg

lemma embedding.nhds_eq_comap (a : α) : nhds a = comap g (nhds $ g a) :=
by rw [eg.induced, nhds_induced]

include eh

lemma embedding.tendsto_iff (H : h ∘ f = i ∘ g) (a : α) : continuous_at i (g a) → continuous_at f a:=
begin
  let N := nhds a, let Nf := nhds (f a),
  let Nhf := nhds (h $ f a), let Ng := nhds (g a),
  have Neq1 : Nf = comap h Nhf, from eh.nhds_eq_comap (f a),
  have Neq2 : N = comap g Ng, from eg.nhds_eq_comap a,
  intro hyp,
  replace hyp : Ng ≤ comap i Nhf,
  { unfold continuous_at at hyp,
    rw ← show h (f a) = i (g a), from congr_fun H a at hyp,
    rwa tendsto_iff_comap at hyp },
  rw calc
      continuous_at f a ↔ tendsto f N Nf : iff.rfl
      ... ↔ N ≤ comap f Nf : tendsto_iff_comap
      ... ↔ comap g Ng ≤ comap f (comap h Nhf) : by rw [Neq1, Neq2]
      ... ↔ comap g Ng ≤ comap g (comap i Nhf) : by rw comap_comm H,
  exact comap_mono hyp
end
end
end

namespace dense_inducing
open set function filter
variables {α : Type*} {β : Type*} {δ : Type*} {γ : Type*}
variables [topological_space α] [topological_space β] [topological_space δ] [topological_space γ]

/-
    f
  α → β
g ↓   ↓ h
  γ → δ
    i
-/
variables {f : α → β} {g : α → γ} {i : γ → δ} {h : β → δ}

lemma comp (dh : dense_inducing h) (df : dense_inducing f) : dense_inducing (h ∘ f) :=
{ dense := dense_range.comp _ dh.dense df.dense dh.continuous,
  induced := (dh.to_inducing.comp df.to_inducing).induced }

lemma of_comm_square (dg : dense_inducing g) (di : dense_inducing i)
  (dh : dense_inducing h) (H : h ∘ f = i ∘ g) : dense_inducing f :=
have dhf : dense_inducing (h ∘ f),
  by {rw H, exact di.comp dg },
{ dense := begin
    intro x,
    have H := dhf.dense (h x),
    rw mem_closure_iff_nhds at H ⊢,
    intros t ht,
    rw [dh.nhds_eq_comap x, mem_comap_sets] at ht,
    rcases ht with ⟨u, hu, hinc⟩,
    replace H := H u hu,
    rw ne_empty_iff_exists_mem at H ⊢,
    rcases H with ⟨v, hv1, a, rfl⟩,
    use f a,
    split, swap, apply mem_range_self,
    apply mem_of_mem_of_subset _ hinc,
    rwa mem_preimage,
  end ,
--  inj := λ a b H, dhf.inj (by {show h (f a) = _, rw H}),
  induced := by rw [dg.induced, di.induced, induced_compose, ← H, ← induced_compose, dh.induced] }
end dense_inducing

namespace dense_embedding
open set function filter
variables {α : Type*} {β : Type*} {δ : Type*} {γ : Type*}

variables [topological_space α] [topological_space β] [topological_space δ] [topological_space γ]

/-
    f
  α → β
g ↓   ↓ h
  γ → δ
    i
-/
variables {f : α → β} {g : α → γ} {i : γ → δ} {h : β → δ}

-- TODO: fix implicit argument in dense_range.comp before PRing

lemma comp (dh : dense_embedding h) (df : dense_embedding f) : dense_embedding (h ∘ f) :=
{ dense := dense_range.comp _ dh.dense df.dense dh.to_dense_inducing.continuous,
  inj :=  function.injective_comp dh.inj df.inj,
  induced := (dh.to_inducing.comp df.to_inducing).induced }

lemma of_homeo (h : α ≃ₜ β) : dense_embedding h :=
{ dense := (dense_range_iff_closure_eq _).mpr $
             (range_iff_surjective.mpr h.to_equiv.surjective).symm ▸ closure_univ,
  inj := h.to_equiv.injective,
  induced := h.induced_eq.symm, }

lemma of_comm_square (dg : dense_embedding g) (di : dense_embedding i)
  (dh : dense_embedding h) (H : h ∘ f = i ∘ g) : dense_embedding f :=
{ inj := begin
    intros a b hab,
    have : (h ∘ f) a = (h ∘ f) b := by convert congr_arg h hab,
    rw H at this,
    exact dg.inj (di.inj this),
  end,
  ..dense_inducing.of_comm_square dg.to_dense_inducing di.to_dense_inducing dh.to_dense_inducing H }
end dense_embedding

section
open filter
variables  {α : Type*} [topological_space α] {β : Type*} [topological_space β] [discrete_topology β]

lemma continuous_into_discrete_iff (f : α → β) : continuous f ↔ ∀ b : β, is_open (f ⁻¹' {b}) :=
begin
  split,
  { intros hf b,
    exact hf _ (is_open_discrete _) },
  { intro h,
    rw continuous_iff_continuous_at,
    intro x,
    have key : f ⁻¹' {f x} ∈ nhds x,
      from mem_nhds_sets (h $ f x) (set.mem_insert (f x) ∅),
    calc map f (nhds x) ≤ pure (f x) : (tendsto_pure f (nhds x) (f x)).2 key
        ... ≤ nhds (f x) : pure_le_nhds _ }
end
end

-- tools for proving that a product of top rings is a top ring
def continuous_pi₁ {I : Type*} {R : I → Type*} {S : I → Type*}
  [∀ i, topological_space (R i)] [∀ i, topological_space (S i)]
  {f : Π (i : I), (R i) → (S i)} (Hfi : ∀ i, continuous (f i)) :
  continuous (λ rs i, f i (rs i) : (Π (i : I), R i) → Π (i : I), S i) :=
continuous_pi (λ i,  (Hfi i).comp (continuous_apply i))

def continuous_pi₂ {I : Type*} {R : I → Type*} {S : I → Type*} {T : I → Type*}
  [∀ i, topological_space (R i)] [∀ i, topological_space (S i)] [∀ i, topological_space (T i)]
  {f : Π (i : I), (R i) × (S i) → (T i)} (Hfi : ∀ i, continuous (f i)) :
continuous (λ rs i, f i ⟨rs.1 i, rs.2 i⟩ : (Π (i : I), R i) × (Π (i : I), S i) → Π (i : I), T i) :=
continuous_pi (λ i, (Hfi i).comp
  (continuous.prod_mk ((continuous_apply i).comp continuous_fst) $
                      (continuous_apply i).comp continuous_snd))


section bases
open filter set
variables {α : Type*} {ι : Type*} {s : ι → set α} [inhabited ι]
lemma generate_eq_of_base (H : ∀ i j, ∃ k, s k ⊆ s i ∩ s j) (U : set α) :
  U ∈ generate (range s) ↔ ∃ i, s i ⊆ U :=
begin
  split ; intro h,
  { induction h with U U_in U V U_gen UV U_union U V U_gen V_gen U_union V_union,
    { rcases U_in with ⟨i, rfl⟩,
      use i },
    { use default ι,
      exact (univ_mem_sets : univ ∈ principal (s $ default ι))},
    { cases U_union with i Ui,
      use i,
      exact subset.trans Ui UV },
    { cases U_union with i Ui,
      cases V_union with j Vj,
      cases H i j with k k_sub,
      use k,
      cases subset_inter_iff.1 k_sub with ki kj,
      exact subset_inter_iff.2 ⟨subset.trans ki Ui, subset.trans kj Vj⟩ }},
  { cases h with i Ui,
    exact generate_sets.superset (generate_sets.basic $ mem_range_self i) Ui },
end

lemma mem_infi_range_of_base (H : ∀ i j, ∃ k, s k ⊆ s i ∩ s j) (U : set α) :
  U ∈ (⨅ i, principal (s i)) ↔ ∃ i, s i ⊆ U :=
begin
  rw mem_infi,
  { split,
    { exact λ ⟨_, ⟨i, rfl⟩, Ui⟩, ⟨i, Ui⟩ },
    { rintro ⟨i, Ui⟩,
      rw mem_Union,
      use [i, Ui] } },
  { rintros i j,
    cases H i j with k k_sub,
    use k,
    split ; apply principal_mono.2 ; simp [set.subset_inter_iff.1 k_sub] },
  { apply_instance }
end

lemma generate_eq_infi (H : ∀ i j, ∃ k, s k ⊆ s i ∩ s j) :
  generate (range s) = ⨅ i, principal (s i) :=
by ext t ; rw [generate_eq_of_base H, mem_infi_range_of_base H]

end bases

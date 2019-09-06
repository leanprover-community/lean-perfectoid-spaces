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


/-
The following class probably won't have global instances, but is meant to model proofs where
we implictly fix a neighborhood filter basis.
-/

class nhds_basis (α : Type*) [topological_space α] :=
(B : α → filter_basis α)
(is_nhds : ∀ x, 𝓝 x = (B x).filter)

namespace nhds_basis
open filter set

variables {α : Type*} {ι : Type*} [topological_space α] [nhds_basis α]
variables {β : Type*} [topological_space β] {δ : Type*}

lemma mem_nhds_iff (x : α) (U : set α) : U ∈ 𝓝 x ↔ ∃ V ∈ B x, V ⊆ U :=
by rw [is_nhds x, filter_basis.mem_filter]

lemma mem_nhds_of_basis {x : α} {U : set α} (U_in : U ∈ B x) : U ∈ 𝓝 x :=
(is_nhds x).symm ▸ filter_basis.mem_filter_of_mem U_in

lemma tendsto_from {f : α → δ} {x : α} {y : filter δ} :
  tendsto f (𝓝 x) y ↔ ∀ {V}, V ∈ y → ∃ U ∈ B x, U ⊆ f ⁻¹' V :=
by split ; intros h V V_in ; specialize h V_in ; rwa [← mem_nhds_iff x] at *

lemma continuous_from {f : α → β} : continuous f ↔ ∀ x, ∀ {V}, V ∈ 𝓝 f x → ∃ U ∈ B x, U ⊆ f ⁻¹' V :=
by simp [continuous_iff_continuous_at, continuous_at, tendsto_from]

lemma tendsto_into {f : δ → α} {x : filter δ} {y : α} : tendsto f x 𝓝 y ↔ ∀ U ∈ B y, f ⁻¹' U ∈ x :=
begin
  split ; intros h,
  { rintro U U_in,
    exact h (mem_nhds_of_basis U_in)  },
  { intros V V_in,
    rcases (mem_nhds_iff _ _).1 V_in with ⟨W, W_in, hW⟩,
    filter_upwards [h W W_in],
    exact preimage_mono hW }
end

lemma continuous_into {f : β → α} : continuous f ↔ ∀ x, ∀ U ∈ B (f x), f ⁻¹' U ∈ 𝓝 x :=
by simp [continuous_iff_continuous_at, continuous_at, tendsto_into]

lemma tendsto_both [nhds_basis β] {f : α → β} {x : α} {y : β} :
  tendsto f (𝓝 x) 𝓝 y ↔ ∀ U ∈ B y, ∃ V ∈ B x, V ⊆ f ⁻¹' U :=
begin
  rw tendsto_into,
  split ; introv h U_in ; specialize h U U_in ; rwa mem_nhds_iff x at *
end

lemma continuous_both [nhds_basis β] {f : α → β} :
  continuous f ↔ ∀ x, ∀ U ∈ B (f x), ∃ V ∈ B x, V ⊆ f ⁻¹' U :=
by simp [continuous_iff_continuous_at, continuous_at, tendsto_both]

end nhds_basis

lemma dense_range.mem_nhds {α : Type*} [topological_space α] {β : Type*} [topological_space β]
  {f : α → β} (h : dense_range f) {b : β} {U : set β} (U_in : U ∈ nhds b) :
  ∃ a : α, f a ∈ U :=
begin
  rcases exists_mem_of_ne_empty (mem_closure_iff_nhds.mp
    (((dense_range_iff_closure_eq f).mp h).symm ▸ mem_univ b : b ∈ closure (range f)) U U_in)
    with ⟨_, h, a, rfl⟩,
  exact ⟨a, h⟩
end

lemma mem_closure_union {α : Type*} [topological_space α] {s₁ s₂ : set α} {x : α}
  (h : x ∈ closure (s₁ ∪ s₂)) (h₁ : -s₁ ∈ 𝓝 x) : x ∈ closure s₂ :=
begin
  rw closure_eq_nhds at *,
  have := calc
    𝓝 x ⊓ principal (s₁ ∪ s₂) = 𝓝 x ⊓ (principal s₁ ⊔ principal s₂) : by rw sup_principal
    ... = (𝓝 x ⊓ principal s₁) ⊔ (𝓝 x ⊓ principal s₂) : by rw lattice.inf_sup_left
    ... = ⊥ ⊔ 𝓝 x ⊓ principal s₂ : by rw inf_principal_eq_bot h₁
    ... = 𝓝 x ⊓ principal s₂ : by rw lattice.bot_sup_eq,
  dsimp,
  rwa ← this
end

open lattice

lemma mem_closure_image {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  {f : α → β} {x : α} {s : set α} (hf : continuous_at f x) (hx : x ∈ closure s) :
  f x ∈ closure (f '' s) :=
begin
  rw [closure_eq_nhds, mem_set_of_eq] at *,
  rw ← bot_lt_iff_ne_bot,
  calc
    ⊥   < map f (𝓝 x ⊓ principal s) : bot_lt_iff_ne_bot.mpr (map_ne_bot hx)
    ... ≤ (map f 𝓝 x) ⊓ (map f $ principal s) : map_inf_le _ _ _
    ... = (map f 𝓝 x) ⊓ (principal $ f '' s) : by rw map_principal
    ... ≤ 𝓝 (f x) ⊓ (principal $ f '' s) : inf_le_inf hf (le_refl _)
end


lemma continuous_at.prod_mk {α : Type*} {β : Type*} {γ : Type*} [topological_space α]
  [topological_space β] [topological_space γ] {f : γ → α} {g : γ → β} {x : γ}
  (hf : continuous_at f x) (hg : continuous_at g x) : continuous_at (λ x, prod.mk (f x) $ g x) x :=
calc
  map (λ (x : γ), (f x, g x)) (𝓝 x) ≤ (map f 𝓝 x).prod (map g 𝓝 x) : filter.map_prod_mk _ _ _
  ... ≤ (𝓝 f x).prod (𝓝 g x) : filter.prod_mono hf hg
  ... = 𝓝 (f x, g x) : by rw nhds_prod_eq

lemma continuous_at.congr_aux {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  {f g : α → β} {a : α}  (h : {x | f x = g x } ∈ 𝓝 a) (hf : continuous_at f a) : continuous_at g a :=
begin
  intros U U_in,
  rw show g a = f a, from (mem_of_nhds h).symm at U_in,
  let V := {x : α | g x ∈ U} ∩ {x | f x = g x},
  suffices : V ∈ 𝓝 a,
  { rw mem_map,
    exact mem_sets_of_superset this (inter_subset_left _ _) },
  have : V = {x : α | f x ∈ U} ∩ {x | f x = g x},
  { ext x,
    split ; rintros ⟨hl, hr⟩ ; rw mem_set_of_eq at hr hl ;
    [ rw ← hr at hl, rw hr at hl ] ; exact ⟨hl, hr⟩ },
  rw this,
  exact filter.inter_mem_sets (hf U_in) ‹_›
end

lemma continuous_at.congr {α : Type*} {β : Type*} [topological_space α] [topological_space β]
  {f g : α → β} {a : α}  (h : {x | f x = g x } ∈ 𝓝 a) : continuous_at f a ↔ continuous_at g a :=
begin
  split ; intro h',
  { exact continuous_at.congr_aux h h' },
  { apply continuous_at.congr_aux _ h',
    convert h,
    ext x,
    rw eq_comm }
end

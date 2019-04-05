import tactic.ring
import topology.algebra.group_completion topology.algebra.ring

import for_mathlib.uniform_space.group

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

open classical set lattice filter topological_space add_comm_group
local attribute [instance] classical.prop_decidable
noncomputable theory

namespace uniform_space.completion
open dense_embedding uniform_space
variables (α : Type*) [ring α] [uniform_space α] [uniform_add_group α] [topological_ring α] [separated α]

instance is_Z_bilin_mul : is_Z_bilin (λp:α×α, p.1 * p.2) :=
⟨assume a a' b, add_mul a a' b, assume a b b', mul_add a b b'⟩

instance : has_one (completion α) := ⟨(1:α)⟩

instance : has_mul (completion α) :=
⟨λa b, extend (dense_embedding_coe.prod dense_embedding_coe)
  ((coe : α → completion α) ∘ (λp:α×α, p.1 * p.2)) (a, b)⟩

lemma coe_one : ((1 : α) : completion α) = 1 := rfl

lemma continuous_mul' : continuous (λp:completion α×completion α, p.1 * p.2) :=
suffices continuous $ extend (dense_embedding_coe.prod dense_embedding_coe) $
  ((coe : α → completion α) ∘ (λp:α×α, p.1 * p.2)),
{ convert this, ext ⟨a, b⟩, refl },
extend_Z_bilin dense_embedding_coe dense_embedding_coe (continuous.comp continuous_mul' (continuous_coe α))

section rules
variables {α}
lemma coe_mul (a b : α) : ((a * b : α) : completion α) = a * b :=
eq.symm (extend_e_eq (dense_embedding_coe.prod dense_embedding_coe) (a, b))

lemma continuous_mul {β : Type*} [topological_space β] {f g : β → completion α}
  (hf : continuous f) (hg : continuous g) : continuous (λb, f b * g b) :=
(continuous.prod_mk hf hg).comp (continuous_mul' α)
end rules

instance : ring (completion α) :=
{ one_mul       := assume a, completion.induction_on a
    (is_closed_eq (continuous_mul continuous_const continuous_id) continuous_id)
    (assume a, by rw [← coe_one, ← coe_mul, one_mul]),
  mul_one       := assume a, completion.induction_on a
    (is_closed_eq (continuous_mul continuous_id continuous_const) continuous_id)
    (assume a, by rw [← coe_one, ← coe_mul, mul_one]),
  mul_assoc     := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_mul (continuous_mul continuous_fst (continuous_snd.comp continuous_fst))
        (continuous_snd.comp continuous_snd))
      (continuous_mul continuous_fst
        (continuous_mul (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_mul, ← coe_mul, ← coe_mul, ← coe_mul, mul_assoc]),
  left_distrib  := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_mul continuous_fst (continuous_add
        (continuous_snd.comp continuous_fst)
        (continuous_snd.comp continuous_snd)))
      (continuous_add
        (continuous_mul continuous_fst (continuous_snd.comp continuous_fst))
        (continuous_mul continuous_fst (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ←coe_add, mul_add]),
  right_distrib := assume a b c, completion.induction_on₃ a b c
    (is_closed_eq
      (continuous_mul (continuous_add continuous_fst
        (continuous_snd.comp continuous_fst)) (continuous_snd.comp continuous_snd))
      (continuous_add
        (continuous_mul continuous_fst (continuous_snd.comp continuous_snd))
        (continuous_mul (continuous_snd.comp continuous_fst) (continuous_snd.comp continuous_snd))))
    (assume a b c, by rw [← coe_add, ← coe_mul, ← coe_mul, ← coe_mul, ←coe_add, add_mul]),
  ..completion.add_comm_group, ..completion.has_mul α, ..completion.has_one α }

instance top_ring_compl : topological_ring (completion α) :=
{ continuous_add := continuous_add',
  continuous_mul := uniform_space.completion.continuous_mul' α,
  continuous_neg := continuous_neg' }

instance is_ring_hom_coe : is_ring_hom (coe : α → completion α) :=
⟨coe_one α, assume a b, coe_mul a b, assume a b, coe_add a b⟩
universe u
instance is_ring_hom_extension
  {β : Type u} [uniform_space β] [ring β] [uniform_add_group β] [topological_ring β]
    [complete_space β] [separated β]
  {f : α → β} [is_ring_hom f] (hf : continuous f) :
  is_ring_hom (completion.extension f) :=
have hf : uniform_continuous f, from uniform_continuous_of_continuous hf,
{ map_one := by rw [← coe_one, extension_coe hf, is_ring_hom.map_one f],
  map_add := assume a b, completion.induction_on₂ a b
    (is_closed_eq
      (continuous_add'.comp continuous_extension)
      (continuous_add (continuous_fst.comp continuous_extension) (continuous_snd.comp continuous_extension)))
    (assume a b,
      by rw [← coe_add, extension_coe hf, extension_coe hf, extension_coe hf, is_add_group_hom.add f]),
  map_mul := assume a b, completion.induction_on₂ a b
    (is_closed_eq
      ((continuous_mul' α).comp continuous_extension)
      (_root_.continuous_mul (continuous_fst.comp continuous_extension) (continuous_snd.comp continuous_extension)))
    (assume a b,
      by rw [← coe_mul, extension_coe hf, extension_coe hf, extension_coe hf, is_ring_hom.map_mul f]) }
end uniform_space.completion


section ring_sep_quot
open uniform_space
variables {α : Type*} [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α]
variables {β : Type*} [comm_ring β] [uniform_space β] [uniform_add_group β] [topological_ring β]

local attribute [instance] separation_setoid

lemma separated_map_mul : separated_map₂ ((*) : α → α → α) :=
begin
  rintros ⟨x, y⟩ ⟨x', y'⟩ h,
  cases uniform_space.separation_prod.1 h with hx hy, clear h,
  unfold function.uncurry has_equiv.equiv setoid.r at *,
  rw group_separation_rel x x' at hx,
  rw group_separation_rel y y' at hy,
  rw group_separation_rel (x*y) _,
  rw show x*y - x'*y' = (x - x')*y + x'*(y - y'), by ring,
  let I := ideal.closure (⊥ : ideal α),
  exact I.add_mem (I.mul_mem_right hx) (I.mul_mem_left hy)
end

instance : comm_ring (sep_quot α) :=
{ mul := sep_quot.map₂ (*),
  one := ⟦1⟧,
  one_mul := begin
    change ∀ a : sep_quot α, sep_quot.map₂ (*) ⟦1⟧ a = id a,
    rw ←sep_quot.map_id,
    exact sep_quot.map₂_const_left_eq_map separated_map_mul uniform_continuous_id.separated_map _ one_mul
  end,
  mul_one := begin
    change ∀ a : sep_quot α, sep_quot.map₂ (*) a ⟦1⟧ = id a,
    rw ←sep_quot.map_id,
    exact sep_quot.map₂_const_right_eq_map separated_map_mul uniform_continuous_id.separated_map _ mul_one
  end,
  mul_assoc := begin
    apply sep_quot.map₂_assoc ; try { exact separated_map_mul },
    exact mul_assoc
  end,
  mul_comm := sep_quot.map₂_comm separated_map_mul mul_comm,
  left_distrib := begin
    apply sep_quot.map₂_left_distrib ; try { exact separated_map_mul <|> exact uniform_continuous₂_add.separated_map},
    exact left_distrib
  end,
  right_distrib := begin
    apply sep_quot.map₂_right_distrib ; try { exact separated_map_mul <|> exact uniform_continuous₂_add.separated_map},
    exact right_distrib
  end,
  ..uniform_space.sep_quot.add_comm_group }


lemma continuous₂_mul {α : Type*} [ring α] [topological_space α] [topological_ring α] : continuous₂ ((*) : α → α → α) :=
begin
  dsimp [continuous₂],
  convert @continuous_mul' α _ _ _,
  ext x,
  cases x,
  refl
end

instance : topological_ring (sep_quot α) :=
{ continuous_add := continuous_add',
  continuous_mul := by rw ←continuous₂_curry ; exact sep_quot.continuous_map₂ continuous₂_mul,
  continuous_neg := continuous_neg' }

instance sep_quot.is_ring_hom_mk : is_ring_hom (quotient.mk : α → sep_quot α) :=
{ map_one := rfl,
  map_mul := λ x y, eq.symm (sep_quot.map₂_mk_mk separated_map_mul x y),
  map_add := is_add_group_hom.add _ }

-- Turning the following into an instance wouldn't work because of the continuity assumption
def sep_quot.is_ring_hom_lift [separated β] {f : α → β} [hom : is_ring_hom f] (hf : continuous f) : is_ring_hom (sep_quot.lift f) :=
have sep : separated_map f, from separated_of_group_hom hf,
{ map_one := by change sep_quot.lift f ⟦1⟧ = 1 ; rw [sep_quot.lift_mk sep, hom.map_one ],
  map_mul := begin rintro ⟨x⟩ ⟨y⟩,  rw [quot_mk_quotient_mk, quot_mk_quotient_mk, ←sep_quot.is_ring_hom_mk.map_mul],
    repeat {rw sep_quot.lift_mk sep} , rw hom.map_mul, end,
  map_add := by haveI := sep_quot.is_add_group_hom_lift hf ; exact is_add_group_hom.add _ }

-- Turning the following into an instance wouldn't work because of the continuity assumption
def sep_quot.is_ring_hom_map {f : α → β} [is_ring_hom f] (hf : continuous f) : is_ring_hom (sep_quot.map f) :=
sep_quot.is_ring_hom_lift (hf.comp continuous_quotient_mk)

end ring_sep_quot

namespace uniform_space.completion
universes u v
open uniform_space
open uniform_space.completion
variables {α : Type u} [uniform_space α]

lemma extension_unique {β : Type*} [uniform_space β] [separated β] [complete_space β]
  {f : α → β} (hf : uniform_continuous f)
  {g : completion α → β} (hg : uniform_continuous g)
  (h : ∀ a : α, f a = g a) : completion.extension f = g :=
begin
  apply completion.ext uniform_continuous_extension.continuous hg.continuous,
  intro a,
  rw extension_coe hf,
  exact h a
end

variables (α) [ring α] [uniform_add_group α] [topological_ring α] [separated α]

instance is_ring_hom_map
  {β : Type v} [uniform_space β] [ring β] [uniform_add_group β] [topological_ring β]
    [separated β]
  {f : α → β} [is_ring_hom f] (hf : continuous f) :
  is_ring_hom (completion.map f) :=
completion.is_ring_hom_extension α (hf.comp (continuous_coe β))

end uniform_space.completion

section ring_completion
open uniform_space

variables (α : Type*)  [uniform_space α]

def ring_completion := completion (sep_quot α)

local attribute [instance] separation_setoid
instance : has_coe α (ring_completion α) := ⟨quotient.mk ∘ Cauchy.pure_cauchy ∘ quotient.mk⟩

instance : uniform_space (ring_completion α) :=
by dunfold ring_completion ; apply_instance

instance : separated (ring_completion α) :=
by dunfold ring_completion ; apply_instance
end ring_completion

namespace ring_completion
open uniform_space
variables {α : Type*}  [uniform_space α]
variables {β : Type*}  [uniform_space β]

lemma uniform_continuous_coe : uniform_continuous (coe : α → ring_completion α) :=
completion.uniform_continuous_coe _

lemma continuous_coe : continuous (coe : α → ring_completion α) :=
completion.continuous_coe _

def extension [separated β] [complete_space β] (f : α → β) : ring_completion α → β :=
completion.extension $ sep_quot.lift f

def uniform_continuous_extension [separated β] [complete_space β] (f : α → β) :
  uniform_continuous (extension f):=
completion.uniform_continuous_extension

def continuous_extension [separated β] [complete_space β] (f : α → β) :
  continuous (extension f):=
(ring_completion.uniform_continuous_extension f).continuous

lemma extension_coe [separated β] [complete_space β] {f : α → β} (hf : uniform_continuous f) (a : α) :
  (ring_completion.extension f) a = f a :=
begin
  convert completion.extension_coe (sep_quot.uniform_continuous_lift hf) _,
  rw sep_quot.lift_mk hf.separated_map,
end

local attribute [instance] separation_setoid


lemma ext [t2_space β] {f g : ring_completion α → β} (hf : continuous f) (hg : continuous g)
  (h : ∀ a : α, f a = g a) : f = g :=
completion.ext hf hg (by rintro ⟨a⟩ ; exact h a)

lemma extension_unique [separated β] [complete_space β]
  {f : α → β} (hf : uniform_continuous f)
  {g : ring_completion α → β} (hg : uniform_continuous g)
  (h : ∀ a : α, f a = g a) : ring_completion.extension f = g :=
begin
  apply completion.extension_unique (sep_quot.uniform_continuous_lift hf) hg,
  rintro ⟨a⟩,
  change sep_quot.lift f ⟦a⟧ = g _,
  rw sep_quot.lift_mk hf.separated_map,
  apply h,
end

def map (f : α → β) : ring_completion α → ring_completion β := completion.map $ sep_quot.map f

@[simp] lemma map_id : map (id : α → α) = id :=
by { delta map, rw sep_quot.map_id, exact completion.map_id }

@[simp] lemma map_comp {γ : Type*} [uniform_space γ]
  {f : α → β} {g : β → γ} (hf : uniform_continuous f) (hg : uniform_continuous g) :
  map (g ∘ f) = map g ∘ map f :=
begin
  delta map,
  rw [completion.map_comp, sep_quot.map_comp];
  solve_by_elim [sep_quot.uniform_continuous_map, uniform_continuous.separated_map]
end

lemma map_uniform_continuous {f : α → β} (hf : uniform_continuous f) : uniform_continuous (map f) :=
completion.uniform_continuous_map

lemma map_unique {f : α → β} (hf : uniform_continuous f) {g : ring_completion α → ring_completion β}
  (hg : uniform_continuous g) (h : ∀ a : α, (f a : ring_completion β) = g a) : map f = g :=
completion.map_unique hg $
begin
  rintro ⟨a⟩,
  change ↑(sep_quot.map f ⟦a⟧) = _,
  rw sep_quot.map_mk hf.separated_map,
  apply h,
end
end ring_completion

section ring_completion
open uniform_space ring_completion
variables (α : Type*) [comm_ring α] [uniform_space α] [uniform_add_group α] [topological_ring α]
variables (β : Type*) [comm_ring β] [uniform_space β] [uniform_add_group β] [topological_ring β]

instance : ring (ring_completion α) :=
by dunfold ring_completion ; apply_instance

instance : topological_ring (ring_completion α) :=
by dunfold ring_completion ; apply_instance

variables {f : α → β} [is_ring_hom f] (hf : continuous f)
include hf

lemma ring_completion.extension_is_ring_hom [separated β] [complete_space β] :
  is_ring_hom (ring_completion.extension f) :=
by haveI := sep_quot.is_ring_hom_lift hf ;
  exact uniform_space.completion.is_ring_hom_extension (sep_quot α) (sep_quot.continuous_lift hf)

lemma ring_completion.map_is_ring_hom : is_ring_hom (ring_completion.map f) :=
by haveI := sep_quot.is_ring_hom_map hf ;
  exact completion.is_ring_hom_map (sep_quot α) (sep_quot.continuous_map hf)

omit hf

def completion_of_complete_separated [complete_space α] [separated α] : α ≃ (ring_completion α) :=
{ to_fun := coe,
  inv_fun := ring_completion.extension id,
  left_inv := ring_completion.extension_coe uniform_continuous_id,
  right_inv :=
  begin
    apply congr_fun,
    change coe ∘ (extension id) = id,
    refine ext ((continuous_extension id).comp continuous_coe) continuous_id _,
    intro x,
    change coe ((extension id) ↑x) = id ↑x,
    rw ring_completion.extension_coe uniform_continuous_id,
    simp,
  end }

lemma uniform_continuous_completion_equiv [complete_space α] [separated α] :
  uniform_continuous (completion_of_complete_separated α).to_fun :=
completion.uniform_continuous_coe _

lemma uniform_continuous_completion_equiv_symm [complete_space α] [separated α] :
  uniform_continuous ⇑(completion_of_complete_separated α).symm :=
completion.uniform_continuous_extension
end ring_completion

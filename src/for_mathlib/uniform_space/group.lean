import topology.algebra.group_completion

import for_mathlib.uniform_space.separation

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable


section uniform_add_group_sep_quot
open uniform_space
variables {α : Type*} [add_group α] [uniform_space α] [uniform_add_group α]
variables {β : Type*} [add_group β] [uniform_space β] [uniform_add_group β]

lemma separated_of_group_hom {f : α → β} [is_add_group_hom f] (hf : continuous f) :
  separated_map f := (uniform_continuous_of_continuous hf).separated_map

lemma uniform_continuous₂_add : uniform_continuous₂ ((+) : α → α → α) :=
uniform_continuous_add'

local attribute [instance] separation_setoid

instance uniform_space_sep_quot.add_group : add_group (sep_quot α) :=
{ add := sep_quot.map₂ (+),
  add_assoc := begin
    apply sep_quot.map₂_assoc ; try { exact uniform_continuous₂_add.separated_map },
    exact add_assoc
  end,
  zero := ⟦0⟧,
  zero_add := begin
    change ∀ a : sep_quot α, sep_quot.map₂ has_add.add ⟦0⟧ a = id a,
    rw ←sep_quot.map_id,
    exact sep_quot.map₂_const_left_eq_map uniform_continuous₂_add.separated_map
      uniform_continuous_id.separated_map _ zero_add
  end,
  add_zero := begin
    change ∀ a : sep_quot α, sep_quot.map₂ has_add.add a ⟦0⟧ = id a,
    rw ←sep_quot.map_id,
    exact sep_quot.map₂_const_right_eq_map  uniform_continuous₂_add.separated_map
      uniform_continuous_id.separated_map _ add_zero
  end,
  neg := sep_quot.map add_group.neg,
  add_left_neg := sep_quot.map₂_map_left_self_const uniform_continuous₂_add.separated_map
    uniform_continuous_neg'.separated_map (0 : α) add_left_neg }

-- MOVEME
theorem uniform_add_group.mk'' {α} [uniform_space α] [add_group α]
  (h₁ : uniform_continuous₂ ((+) : α → α → α))
  (h₂ : uniform_continuous (λp:α, -p)) : uniform_add_group α :=
⟨uniform_continuous.comp h₁ (uniform_continuous.prod_mk uniform_continuous_fst (h₂.comp uniform_continuous_snd))⟩

instance : uniform_add_group (sep_quot α) :=
uniform_add_group.mk'' (sep_quot.uniform_continuous_map₂ uniform_continuous₂_add) (sep_quot.uniform_continuous_map uniform_continuous_neg')

lemma sep_quot.add_mk (a b : α) : ⟦a⟧ + ⟦b⟧ = ⟦a+b⟧ :=
sep_quot.map₂_mk_mk uniform_continuous₂_add.separated_map _ _

instance sep_quot.is_add_group_hom_mk : is_add_group_hom (quotient.mk : α → sep_quot α) :=
⟨λ a b, eq.symm $ sep_quot.add_mk a b⟩

variables {f : α → β}

instance sep_quot.is_add_group_hom_lift [separated β]  [hom : is_add_group_hom f] (hf : continuous f) : is_add_group_hom (sep_quot.lift f) :=
⟨begin
  rintros ⟨a⟩ ⟨b⟩,
  repeat { rw quot_mk_quotient_mk },
  rw [sep_quot.add_mk],
  repeat { rw sep_quot.lift_mk (separated_of_group_hom hf) },
  rw hom.map_add,
end⟩

instance sep_quot.is_add_group_hom_map [hom : is_add_group_hom f](hf : continuous f) : is_add_group_hom (sep_quot.map f) :=
sep_quot.is_add_group_hom_lift (continuous_quotient_mk.comp hf)
end uniform_add_group_sep_quot

section uniform_add_comm_group_sep_quot
open uniform_space
variables {α : Type*} [add_comm_group α] [uniform_space α] [uniform_add_group α]
local attribute [instance] separation_setoid

instance uniform_space.sep_quot.add_comm_group : add_comm_group (sep_quot α) :=
{ add_comm := sep_quot.map₂_comm uniform_continuous₂_add.separated_map add_comm,
  ..uniform_space_sep_quot.add_group, }
end uniform_add_comm_group_sep_quot

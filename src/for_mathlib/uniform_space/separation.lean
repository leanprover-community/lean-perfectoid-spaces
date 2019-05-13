import topology.uniform_space.separation

import for_mathlib.quotient
import for_mathlib.topology
import for_mathlib.uniform_space.basic

noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

open filter

universes u v w

local notation f `∘₂` g := function.bicompr f g

section
variables {α : Type u} {β : Type v} {γ : Type w}
variables [uniform_space α] [uniform_space β] [uniform_space γ]
local attribute [instance] uniform_space.separation_setoid

def uniform_space.separated_map (f : α → β) : Prop := ∀ x y, x ≈ y → f x ≈ f y

def uniform_space.separated_map₂ (f : α → β → γ) : Prop := uniform_space.separated_map (function.uncurry f)

--∀ x x' y y', x ≈ x' → y ≈ y' → f x y ≈ f x' y'

end

local attribute [instance] uniform_space.separation_setoid

section
open uniform_space
variables {α : Type u} {β : Type v} {γ : Type w} {δ : Type*}
variables [uniform_space α] [uniform_space β] [uniform_space γ] [uniform_space δ]

lemma uniform_space.separated_map.comp {f : α → β} {g : β → γ} (hf : separated_map f) (hg : separated_map g) :
separated_map (g ∘ f) := assume x y h, hg _ _ (hf x y h)

lemma uniform_space.separated_map.comp₂ {f : α → β → γ} {g : γ → δ} (hf : separated_map₂ f) (hg : separated_map g) :
separated_map₂ (g ∘₂ f) :=
begin
  unfold separated_map₂,
  rw function.uncurry_bicompr,
  exact hf.comp hg
end

lemma uniform_space.separated_map.eqv_of_separated {f : α → β} {x y : α} (hf : uniform_space.separated_map f)
  (h : x ≈ y) : f x ≈ f y := hf x y h

lemma uniform_space.separated_map.eq_of_separated [separated β] {f : α → β} {x y : α} (hf : uniform_space.separated_map f)
  (h : x ≈ y) : f x = f y := separated_def.1 ‹_›  _ _ (hf x y h)

lemma uniform_continuous.separated_map {f : α → β} (H : uniform_continuous f) :
  uniform_space.separated_map f := assume x y h s Hs, h _ (H Hs)

lemma uniform_continuous.eqv_of_separated {f : α → β} (H : uniform_continuous f) {x y : α} (h : x ≈ y) :
  f x ≈ f y
 := H.separated_map _ _ h

lemma uniform_continuous.eq_of_separated [separated β] {f : α → β} (H : uniform_continuous f) {x y : α} (h : x ≈ y) :
  f x = f y
 := H.separated_map.eq_of_separated h

lemma separated.eq_iff [separated α] {x y : α} (h : x ≈ y) : x = y :=
separated_def.1 (by apply_instance) x y h
end

open uniform_space

/-- separation space -/
@[reducible]
def sep_quot (α : Type*) [uniform_space α] := quotient (separation_setoid α)

namespace sep_quot
variables {α : Type u} {β : Type v} {γ : Type w}
variables [uniform_space α] [uniform_space β] [uniform_space γ]

def mk {α : Type u} [uniform_space α] : α → sep_quot α := quotient.mk

lemma uniform_embedding [separated α] : uniform_embedding (sep_quot.mk : α → sep_quot α) :=
⟨λ x y h, separated.eq_iff (quotient.exact h), comap_quotient_eq_uniformity⟩

lemma uniform_continuous_mk :
  uniform_continuous (quotient.mk : α → sep_quot α) :=
le_refl _

def lift [separated β] (f : α → β) : sep_quot α → β :=
if h : separated_map f then
  quotient.lift f (λ x x' hxx', h.eq_of_separated hxx')
else
  λ x, f $ habitant_of_quotient_habitant x

lemma continuous_lift [separated β] {f : α → β} (h : continuous f) : continuous (lift f) :=
begin
  by_cases hf : separated_map f,
  { rw [lift, dif_pos hf], apply continuous_quotient_lift _ h, },
  { rw [lift, dif_neg hf], exact continuous_of_const (λ a b, rfl)}
end

lemma uniform_continuous_lift [separated β] {f : α → β} (hf : uniform_continuous f) : uniform_continuous (lift f) :=
by simp [lift, hf.separated_map] ; exact hf

section sep_quot_lift
variables  [separated β] {f : α → β} (h : separated_map f)
include h

lemma lift_mk (x : α) : lift f ⟦x⟧ = f x := by simp[lift, h]

lemma unique_lift {g : sep_quot α → β} (hg : uniform_continuous g) (g_mk : ∀ x, g ⟦x⟧ = f x) : g = lift f :=
begin
  ext a,
  cases quotient.exists_rep a with x hx,
  rwa [←hx, lift_mk h x, g_mk x]
end
end sep_quot_lift

def map (f : α → β) : sep_quot α → sep_quot β := lift (quotient.mk ∘ f)

lemma continuous_map {f : α → β} (h : continuous f) : continuous (map f) :=
continuous_lift $ h.comp continuous_quotient_mk

lemma uniform_continuous_map {f : α → β} (hf : uniform_continuous f): uniform_continuous (map f) :=
uniform_continuous_lift (hf.comp uniform_continuous_mk)

lemma map_mk {f : α → β} (h : separated_map f) (a : α) : map f ⟦a⟧ = ⟦f a⟧ :=
by rw [map, lift_mk (h.comp uniform_continuous_mk.separated_map)]

lemma map_unique {f : α → β} (hf : separated_map f)
  {g : sep_quot α → sep_quot β}
  (comm : quotient.mk ∘ f = g ∘ quotient.mk) : map f = g :=
by ext ⟨a⟩;
calc map f ⟦a⟧ = ⟦f a⟧ : map_mk hf a
  ... = g ⟦a⟧ : congr_fun comm a

@[simp] lemma map_id : map (@id α) = id :=
map_unique uniform_continuous_id.separated_map rfl

lemma map_comp {f : α → β} {g : β → γ} (hf : separated_map f) (hg : separated_map g) :
  map g ∘ map f = map (g ∘ f) :=
(map_unique (hf.comp hg) $ by simp only [(∘), map_mk, hf, hg]).symm

protected def prod  : sep_quot α → sep_quot β → sep_quot (α × β) :=
quotient.lift₂ (λ a b, ⟦(a, b)⟧) $ assume _ _ _ _ h h', quotient.eq.2 (separation_prod.2 ⟨h, h'⟩)

lemma uniform_continuous_prod : uniform_continuous₂ (@sep_quot.prod α β _ _) :=
begin
  unfold uniform_continuous₂,
  unfold uniform_continuous,
  rw [uniformity_prod_eq_prod, uniformity_quotient, uniformity_quotient, filter.prod_map_map_eq,
    filter.tendsto_map'_iff, filter.tendsto_map'_iff, uniformity_quotient, uniformity_prod_eq_prod],
  exact tendsto_map
end

@[simp]
lemma prod_mk_mk (a : α) (b : β) : sep_quot.prod ⟦a⟧ ⟦b⟧ = ⟦(a, b)⟧ := rfl

def lift₂ [separated γ] (f : α → β → γ) : sep_quot α → sep_quot β → γ :=
(lift $ function.uncurry f) ∘₂ sep_quot.prod

lemma uniform_continuous_lift₂ [separated γ] {f : α → β → γ} (hf : uniform_continuous₂ f) :
  uniform_continuous₂ (sep_quot.lift₂ f) :=
uniform_continuous_prod.comp $ uniform_continuous_lift hf

@[simp]
lemma lift₂_mk_mk [separated γ] {f : α → β → γ} (h : separated_map₂ f) (a : α) (b : β) :
  lift₂ f ⟦a⟧ ⟦b⟧ = f a b := lift_mk h _

def map₂ (f : α → β → γ) : sep_quot α → sep_quot β → sep_quot γ :=
lift₂ (quotient.mk ∘₂ f)

lemma uniform_continuous_map₂ {f : α → β → γ} (hf : uniform_continuous₂ f) :
  uniform_continuous₂ (sep_quot.map₂ f) :=
uniform_continuous_lift₂ $ hf.comp uniform_continuous_mk

@[simp]
lemma map₂_mk_mk {f : α → β → γ} (h : separated_map₂ f) (a : α) (b : β) :
  map₂ f ⟦a⟧ ⟦b⟧ = ⟦f a b⟧ :=
lift₂_mk_mk (uniform_continuous_mk.separated_map.comp₂ h) _ _

lemma map₂_unique {f : α → β → γ} (hf : separated_map₂ f)
  {g : sep_quot α → sep_quot β → sep_quot γ}
  (comm : ∀ a b, ⟦f a b⟧ = g  ⟦a⟧ ⟦b⟧) : map₂ f = g :=
by ext ⟨a⟩ ⟨b⟩ ;
   calc map₂ f ⟦a⟧ ⟦b⟧ = ⟦f a b⟧   : map₂_mk_mk hf a b
                   ... = g ⟦a⟧ ⟦b⟧ : comm a b

variables {δ : Type*} {δ' : Type*} {δ'' : Type*} {ε : Type*}
  [uniform_space δ] [uniform_space δ'] [uniform_space δ''] [uniform_space ε]

lemma continuous_map₂ {f : α → β → γ} (h : continuous₂ f) : continuous₂ (map₂ f) :=
begin
  unfold continuous₂ map₂ lift₂,
  rw function.uncurry_bicompr,
  apply continuous.comp uniform_continuous_prod.continuous,
  apply continuous_lift,
  rw function.uncurry_bicompr,
  apply continuous.comp h continuous_quotient_mk
end

-- Now begins a long series of lemmas for which we use an ad hoc killing tactic.

meta def sep_quot_tac : tactic unit :=
`[repeat { rintros ⟨x⟩ },
  repeat { rw quot_mk_quotient_mk },
  repeat { rw map_mk },
  repeat { rw map₂_mk_mk },
  repeat { rw map_mk },
  repeat { rw H },
  repeat { assumption } ]

lemma map₂_const_left_eq_map {f : α → β → γ} (hf : separated_map₂ f)
  {g : β → γ} (hg : separated_map g) (a : α)
  (H : ∀ b, f a b = g b) : ∀ b, map₂ f ⟦a⟧ b = map g b :=
by sep_quot_tac

lemma map₂_const_right_eq_map {f : α → β → γ} (hf : separated_map₂ f)
  {g : α → γ} (hg : separated_map g) (b : β)
  (H : ∀ a, f a b = g a) : ∀ a, map₂ f a ⟦b⟧ = map g a :=
by sep_quot_tac

lemma map₂_map_left_self_const {f : α → β → γ} (hf : separated_map₂ f)
  {g : β → α} (hg : separated_map g) (c : γ)
  (H : ∀ b, f (g b) b = c) : ∀ b, map₂ f (map g b) b = ⟦c⟧ :=
by sep_quot_tac

lemma map₂_map_right_self_const {f : α → β → γ} (hf : separated_map₂ f)
  {g : α → β} (hg : separated_map g) (c : γ)
  (H : ∀ a, f a (g a) = c) : ∀ a, map₂ f a (map g a) = ⟦c⟧ :=
by sep_quot_tac

lemma map₂_comm {f : α → α → β} (hf : separated_map₂ f)
  (H : ∀ a b, f a b = f b a) : ∀ a b, map₂ f a b = map₂ f b a :=
by sep_quot_tac

lemma map₂_assoc {f : α → β → δ} (hf : separated_map₂ f)
  {f' : β  → γ → δ'} (hf' : separated_map₂ f')
  {g : δ → γ → ε} (hg : separated_map₂ g)
  {g' : α → δ' → ε} (hg' : separated_map₂ g')
  (H : ∀ a b c, g (f a b) c = g' a (f' b c)) :
  ∀ a b c, map₂ g (map₂ f a b) c = map₂ g' a (map₂ f' b c) :=
by sep_quot_tac

lemma map₂_left_distrib {f : α → β → δ} (hf : separated_map₂ f)
  {f' : α  → γ → δ'} (hf' : separated_map₂ f')
  {g : δ → δ' → ε} (hg : separated_map₂ g)
  {f'' : β → γ → δ''} (hg : separated_map₂ f'')
  {g' : α → δ'' → ε} (hg : separated_map₂ g')
  (H : ∀ a b c, g' a (f'' b c) = g (f a b) (f' a c)) :
  ∀ a b c, map₂ g' a (map₂ f'' b c) = map₂ g (map₂ f a b) (map₂ f' a c) :=
by sep_quot_tac

lemma map₂_right_distrib {f : α → γ → δ} (hf : separated_map₂ f)
  {f' : β → γ → δ'} (hf' : separated_map₂ f')
  {g : δ → δ' → ε} (hg : separated_map₂ g)
  {f'' : α → β → δ''} (hg : separated_map₂ f'')
  {g' : δ'' → γ → ε} (hg : separated_map₂ g')
  (H : ∀ a b c, g' (f'' a b) c = g (f a c) (f' b c)) :
  ∀ a b c, map₂ g' (map₂ f'' a b) c = map₂ g (map₂ f a c) (map₂ f' b c) :=
by sep_quot_tac
end sep_quot

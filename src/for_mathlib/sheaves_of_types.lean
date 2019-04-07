-- presheaf of types basics and equivalence
-- written by KB, tidied up by Mario

import topology.opens topology.constructions

universes u v u₁ v₁ u₂ v₂

open topological_space

structure presheaf_of_typesU (X : Type u) [topological_space X] :=
(F : opens X → Type u)
(res : ∀ {U V : opens X} (h : V ≤ U), F U → F V)
(id : ∀ (U : opens X) (x : F U), res (le_refl U) x = x)
(comp : ∀ {U V W : opens X} (hUV : V ≤ U) (hVW : W ≤ V) (x : F U),
  res hVW (res hUV x) = res (le_trans hVW hUV) x)

instance (X : Type u) [topological_space X] : has_coe_to_fun (presheaf_of_typesU X) :=
⟨_, presheaf_of_typesU.F⟩

namespace topological_space.opens
variables {α : Type*} {β : Type*} {γ : Type*}
variables [topological_space α] [topological_space β] [topological_space γ]

def comap (f : α → β) (hf : continuous f) (U : opens β) : opens α :=
⟨f ⁻¹' U, hf _ U.2⟩

theorem comap_id (U : opens α) : comap id continuous_id U = U := ext rfl

theorem comap_comp {f : α → β} {g : β → γ}
  {hf : continuous f} {hg : continuous g} (U : opens γ) :
  comap _ (hf.comp hg) U = comap _ hf (comap _ hg U) := ext rfl

theorem comap_mono {α β} [topological_space α] [topological_space β]
  {f : α → β} {hf : continuous f} {U V : opens β}
  (h : U ≤ V) : U.comap f hf ≤ V.comap f hf :=
λ x hx, h hx

end topological_space.opens

namespace presheaf_of_typesU
open topological_space.opens

variables {X : Type u} {Y : Type u} {Z : Type u} {W : Type u}
  [topological_space X] [topological_space Y] [topological_space Z] [topological_space W]
  (ℱ : presheaf_of_typesU X) (𝒢 : presheaf_of_typesU Y) (ℋ : presheaf_of_typesU Z)
  (𝒥 : presheaf_of_typesU W)

@[simp] theorem id' (U : opens X) (x : ℱ.F U) (h) : ℱ.res h x = x := ℱ.id _ _

structure morphism (ℱ 𝒢 : presheaf_of_typesU X) :=
(ρ : ∀ U : opens X, ℱ.F U → 𝒢.F U)
(nat : ∀ U V : opens X, ∀ h : V ≤ U,
   ∀ x : ℱ.F U, ρ V (ℱ.res h x) = 𝒢.res h (ρ U x))

def morphism.id (ℱ : presheaf_of_typesU X) : morphism ℱ ℱ :=
{ ρ := λ U x, x,
  nat := λ U V h x, rfl
}

def morphism.comp (ℱ 𝒢 ℋ : presheaf_of_typesU X) (fℱ𝒢 : morphism ℱ 𝒢) (f𝒢ℋ : morphism 𝒢 ℋ) :
  morphism ℱ ℋ :=
{ ρ := λ U x, f𝒢ℋ.ρ U (fℱ𝒢.ρ U x),
  nat := λ U V h x, by rw [fℱ𝒢.nat, f𝒢ℋ.nat]
}

def pushforward (f : X → Y) [hf : continuous f] (ℱ : presheaf_of_typesU X) :
  presheaf_of_typesU Y :=
{ F := λ V, ℱ.F ⟨f ⁻¹' V, hf _ V.2⟩,
  res := λ _ _ hUV, ℱ.res (λ _ hx, hUV hx),
  id := λ _, ℱ.id _,
  comp := λ U V W hUV hVW, ℱ.comp _ _,
}

structure f_map (𝒢 : presheaf_of_typesU Y) (ℱ : presheaf_of_typesU X) :=
(f : X → Y)
(hf : continuous f)
(ρ : ∀ V : opens Y, 𝒢.F V → ℱ.F (V.comap f hf))
(nat : ∀ U V : opens Y, ∀ hUV : V ≤ U,
  ∀ x : 𝒢.F U, ρ V (𝒢.res hUV x) = ℱ.res (comap_mono hUV) (ρ U x))

namespace f_map

variables {𝒢 ℱ}
theorem ext {α β : f_map 𝒢 ℱ} (hf : α.f = β.f)
  (hρ : ∀ V x, α.ρ V x = ℱ.res (le_of_eq (by congr')) (β.ρ V x)) : α = β :=
begin
  cases α with αf αhf αρ αnat, cases β with βf βhf βρ βnat,
  cases hf,
  congr', funext V x,
  simpa using hρ V x
end
variables (𝒢 ℱ)

def id (ℱ : presheaf_of_typesU X) : f_map ℱ ℱ :=
{ f := λ x, x,
  hf := continuous_id,
  ρ := λ V x, ℱ.res (le_of_eq (comap_id _)) x,
  nat := λ U V hUV x, by rw [ℱ.comp, ℱ.comp] }

def comp {ℱ : presheaf_of_typesU X} {𝒢 : presheaf_of_typesU Y} {ℋ : presheaf_of_typesU Z}
  (fℱ𝒢 : f_map ℱ 𝒢) (f𝒢ℋ : f_map 𝒢 ℋ) : f_map ℱ ℋ :=
{ f := λ z, fℱ𝒢.f (f𝒢ℋ.f z),
  hf := continuous.comp f𝒢ℋ.hf fℱ𝒢.hf,
  ρ := λ U x, ℋ.res (le_of_eq (comap_comp _)) (f𝒢ℋ.ρ _ (fℱ𝒢.ρ U x)),
  nat := λ U V hUV x, by rw [fℱ𝒢.nat, f𝒢ℋ.nat, ℋ.comp, ℋ.comp] }

lemma comp_assoc {ℱ : presheaf_of_typesU X} {𝒢 : presheaf_of_typesU Y} {ℋ : presheaf_of_typesU Z}
  {𝒥 : presheaf_of_typesU W} (fℱ𝒢 : f_map ℱ 𝒢) (f𝒢ℋ  : f_map 𝒢 ℋ) (fℋ𝒥 : f_map ℋ 𝒥) :
  comp (comp fℱ𝒢 f𝒢ℋ) fℋ𝒥 = comp fℱ𝒢 (comp f𝒢ℋ fℋ𝒥) :=
f_map.ext rfl $ λ V x, begin
  simp, dsimp [comp], simp [𝒥.comp], refl
end

lemma id_comp (fℱ𝒢 : f_map ℱ 𝒢) : comp (f_map.id ℱ) fℱ𝒢 = fℱ𝒢 :=
f_map.ext rfl $ λ V x, begin
  simp, dsimp [comp, id], simp [𝒢.comp], rw [fℱ𝒢.nat, 𝒢.id']
end

lemma comp_id (fℱ𝒢 : f_map ℱ 𝒢) : comp fℱ𝒢 (f_map.id 𝒢) = fℱ𝒢 :=
f_map.ext rfl $ λ V x, begin
  simp, dsimp [comp, id], simp [𝒢.comp]
end

end f_map

structure presheaf_of_types_equiv (ℱ : presheaf_of_typesU X) (𝒢 : presheaf_of_typesU Y) :=
(to_fun : f_map ℱ 𝒢)
(inv_fun : f_map 𝒢 ℱ)
(left_inv : f_map.comp inv_fun to_fun = f_map.id 𝒢)
(right_inv : f_map.comp to_fun inv_fun = f_map.id ℱ)

def presheaf_of_types_equiv.refl (ℱ : presheaf_of_typesU X) :
  presheaf_of_types_equiv ℱ ℱ :=
{ to_fun := f_map.id ℱ,
  inv_fun := f_map.id ℱ,
  left_inv := f_map.id_comp _ _ _,
  right_inv := f_map.id_comp _ _ _ }

def presheaf_of_types_equiv.symm (ℱ : presheaf_of_typesU X) (𝒢 : presheaf_of_typesU Y)
  (h : presheaf_of_types_equiv ℱ 𝒢) : presheaf_of_types_equiv 𝒢 ℱ :=
{ to_fun := h.inv_fun,
  inv_fun := h.to_fun,
  left_inv := h.right_inv,
  right_inv := h.left_inv }

--local infix ` ** `:50 := f_map.comp

def presheaf_of_types_equiv.trans (ℱ : presheaf_of_typesU X)
  (𝒢 : presheaf_of_typesU Y)
  (ℋ : presheaf_of_typesU Z)
  (hℱ𝒢 : presheaf_of_types_equiv ℱ 𝒢)
  (h𝒢ℋ : presheaf_of_types_equiv 𝒢 ℋ)
  : presheaf_of_types_equiv ℱ ℋ :=
{ to_fun := f_map.comp hℱ𝒢.to_fun h𝒢ℋ.to_fun,
  inv_fun := f_map.comp h𝒢ℋ.inv_fun hℱ𝒢.inv_fun,
  left_inv := by
    rw [f_map.comp_assoc, ←f_map.comp_assoc hℱ𝒢.inv_fun, hℱ𝒢.left_inv,
    f_map.id_comp, h𝒢ℋ.left_inv],
  right_inv := by
    rw [f_map.comp_assoc, ←f_map.comp_assoc h𝒢ℋ.to_fun,
    h𝒢ℋ.right_inv, f_map.id_comp, hℱ𝒢.right_inv] }

end presheaf_of_typesU

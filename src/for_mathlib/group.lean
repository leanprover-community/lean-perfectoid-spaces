import algebra.group data.equiv.basic

variables (G : Type*) [group G] (H : Type*) [group H]
variables (M : Type*) [monoid M] (N : Type*) [monoid N]

structure group_equiv extends G ≃ H :=
{ hom : is_group_hom to_fun}

instance : has_coe_to_fun (group_equiv G H) :=
{ F := λ _, G → H,
  coe := λ h, h.to_fun }

structure monoid_equiv extends M ≃ N :=
{ hom : is_monoid_hom to_fun}

instance : has_coe_to_fun (monoid_equiv M N) :=
{ F := λ _, M → N,
  coe := λ h, h.to_fun }

variables {G} {H} {M} {N}

namespace monoid_equiv

instance is_monoid_hom' (h : monoid_equiv M N) :
is_monoid_hom h := h.hom

def refl : monoid_equiv M M :=
{ hom := is_monoid_hom.id,
..equiv.refl _}

def symm (h : monoid_equiv M N) : monoid_equiv N M :=
{ hom := { map_one := by rw ←h.hom.map_one; exact (h.left_inv 1),
  map_mul := λ n₁ n₂, function.injective_of_left_inverse h.left_inv begin
   rw h.hom.map_mul, unfold equiv.symm, rw [h.right_inv, h.right_inv, h.right_inv], end }
 ..h.to_equiv.symm}

def trans {P : Type*} [monoid P] (h1 : monoid_equiv N M) (h2 : monoid_equiv M P) :
monoid_equiv N P := {
  hom := is_monoid_hom.comp _ _,
  ..equiv.trans h1.to_equiv h2.to_equiv }

instance symm.is_monoid_hom (h : monoid_equiv M N) :
is_monoid_hom h.symm := h.symm.hom

end monoid_equiv

namespace group_equiv

instance is_group_hom (h : group_equiv G H) :
is_group_hom h := h.hom

def refl : group_equiv G G :=
{ hom := is_group_hom.id, ..equiv.refl _}

def symm (h : group_equiv G H) : group_equiv H G :=
{ hom := { mul := λ n₁ n₂, function.injective_of_left_inverse h.left_inv begin
  rw h.hom.mul, unfold equiv.symm, rw [h.right_inv, h.right_inv, h.right_inv], end }
  ..h.to_equiv.symm}

def trans {K : Type*} [group K] (h1 : group_equiv G H) (h2 : group_equiv H K) :
group_equiv G K := {
  hom := is_group_hom.comp _ _,
  ..equiv.trans h1.to_equiv h2.to_equiv }

instance symm.is_group_hom (h : group_equiv G H) :
is_group_hom h.symm := h.symm.hom

end group_equiv

namespace units

variables {α : Type*} {β : Type*} {γ : Type*} [monoid α] [monoid β] [monoid γ]
(f : α → β) (g : β → γ) [is_monoid_hom f] [is_monoid_hom g]

lemma map_id : map (id : α → α) = id := by ext; refl

lemma map_comp : map (g ∘ f) = map g ∘ map f := rfl

def map_equiv (h : monoid_equiv α β) : group_equiv (units α) (units β) :=
{ to_fun := map h,
  inv_fun := map h.symm,
  left_inv := λ u, ext $ h.left_inv u,
  right_inv := λ u, ext $ h.right_inv u,
  hom := by apply_instance }

end units

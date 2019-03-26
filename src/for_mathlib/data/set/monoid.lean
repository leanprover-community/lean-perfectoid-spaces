import data.set.lattice
import group_theory.subgroup

namespace set

variables {α : Type*}

def one [has_one α] : set α := {(1 : α)}

def mul [has_mul α] (s₁ s₂ : set α) : set α :=
  {x | ∃ (x₁ ∈ s₁) (x₂ ∈ s₂), x = x₁ * x₂}

instance [monoid α] : monoid (set α) :=
{ one := one,
  mul := mul,
  one_mul :=
  begin
    intro s,
    ext r, split; intro h,
    { rcases h with ⟨a,ha,_,_,_⟩,
      erw mem_singleton_iff at ha,
      simp * at * },
    { use [1, mem_singleton 1, r, h],
      simp }
  end,
  mul_one :=
  begin
    intro s,
    ext r, split; intro h,
    { rcases h with ⟨_,_,a,ha,_⟩,
      erw mem_singleton_iff at ha,
      simp * at * },
    { use [r, h, 1, mem_singleton 1],
      simp },
  end,
  mul_assoc := λ s₁ s₂ s₃,
  begin
    ext r, split; intro h;
    [ rcases h with ⟨_, ⟨x, hx, y, hy, rfl⟩, z, hz, rfl⟩,
      rcases h with ⟨x, hx, _, ⟨y, hy, z, hz, rfl⟩, rfl⟩ ];
    [ rw mul_assoc, rw ← mul_assoc ];
    [ exact ⟨x, hx, _, ⟨y, hy, z, hz, rfl⟩, rfl⟩,
      exact ⟨_, ⟨x, hx, y, hy, rfl⟩, z, hz, rfl⟩ ]
  end }

lemma mul_eq_image [monoid α] (s t : set α) : s * t = (λ x : α × α, x.1 * x.2) '' s.prod t :=
begin
  ext x, split,
  { rintros ⟨_, h₁, _, h₂, rfl⟩,
    exact ⟨(_, _), set.mem_prod.mpr ⟨h₁, h₂⟩, rfl⟩ },
  { simp only [mem_image, set.mem_prod],
    rintros ⟨⟨_, _⟩, ⟨h₁, h₂⟩, rfl⟩,
    exact ⟨_, h₁, _, h₂, rfl⟩ }
end

instance [monoid α] : semiring (set α) :=
{ add := (⊔),
  zero := ∅,
  add_assoc := set.union_assoc,
  zero_add := set.empty_union,
  add_zero := set.union_empty,
  add_comm := set.union_comm,
  zero_mul := λ s, set.ext $ λ a, ⟨by rintros ⟨_, _, _, _, rfl⟩; exact false.elim ‹_›, false.elim⟩,
  mul_zero := λ s, set.ext $ λ a, ⟨by rintros ⟨_, _, _, _, rfl⟩; exact false.elim ‹_›, false.elim⟩,
  left_distrib := λ s t u,
  begin
    ext a, split,
    { rintros ⟨_, _, _, H, rfl⟩,
      cases H; [left, right]; exact ⟨_, ‹_›, _, ‹_›, rfl⟩ },
    { intro H,
      cases H with H H;
      rcases H with ⟨_, _, _, _, rfl⟩;
      refine ⟨_, ‹_›, _, _, rfl⟩;
      erw mem_union; simp * }
  end,
  right_distrib := λ s t u,
  begin
    ext a, split,
    { rintros ⟨_, H, _, _, rfl⟩,
      cases H; [left, right]; exact ⟨_, ‹_›, _, ‹_›, rfl⟩ },
    { intro H,
      cases H with H H;
      rcases H with ⟨_, _, _, _, rfl⟩;
      refine ⟨_, _, _, ‹_›, rfl⟩;
      erw mem_union; simp * }
  end,
  ..set.monoid }

instance [comm_monoid α] : comm_semiring (set α) :=
{ mul_comm := λ s t,
  by ext a; split; rintros ⟨_, _, _, _, rfl⟩; rw mul_comm; exact ⟨_, ‹_›, _, ‹_›, rfl⟩,
  ..set.semiring }

variables {β : Type*} (f : α → β) [monoid α] [monoid β] [is_monoid_hom f]

instance : is_semiring_hom (image f) :=
{ map_zero := image_empty _,
  map_one := by erw [image_singleton, is_monoid_hom.map_one f]; refl,
  map_add := image_union _,
  map_mul := λ s t,
  begin
    erw [mul_eq_image, mul_eq_image, prod_image_image_eq, ← image_comp, ← image_comp],
    congr' 1,
    funext x,
    change f (_ * _) = f _ * f _,
    erw [is_monoid_hom.map_mul f]
  end }

end set

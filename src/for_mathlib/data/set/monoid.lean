import data.set.basic

namespace set

variables {R : Type*} [ring R]

def one : set R := {(1 : R)}

def mul (s₁ s₂ : set R) : set R :=
  {x | ∃ (x₁ ∈ s₁) (x₂ ∈ s₂), x = x₁ * x₂}

instance monoid : monoid (set R) :=
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

end set

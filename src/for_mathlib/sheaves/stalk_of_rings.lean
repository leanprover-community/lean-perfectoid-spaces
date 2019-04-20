/-
  Stalk of rings.

  https://stacks.math.columbia.edu/tag/007L
  (just says that the category of rings is a type of algebraic structure)

  Author -- Ramon Fernandez Mir
-/

import topology.basic
import for_mathlib.sheaves.stalk
import for_mathlib.sheaves.presheaf_of_rings

universes u v w

open topological_space

section stalk_of_rings

variables {α : Type u} [topological_space α]
variables (F : presheaf_of_rings α) (x : α)

definition stalk_of_rings := stalk F.to_presheaf x

end stalk_of_rings

-- Stalks are rings.

section stalk_of_rings_is_ring

parameters {α : Type u} [topological_space α]
parameters (F : presheaf_of_rings α) (x : α)

-- Add.

private def stalk_of_rings_add_aux :
stalk.elem F.to_presheaf x →
stalk.elem F.to_presheaf x →
stalk F.to_presheaf x :=
λ s t,
⟦{U := s.U ∩ t.U,
HxU := ⟨s.HxU, t.HxU⟩,
s := F.res s.U _ (set.inter_subset_left _ _) s.s +
     F.res t.U _ (set.inter_subset_right _ _) t.s}⟧

instance stalk_of_rings_has_add : has_add (stalk_of_rings F x) :=
{ add := quotient.lift₂ (stalk_of_rings_add_aux) $
  begin
    intros a1 a2 b1 b2 H1 H2,
    let F' := F.to_presheaf,
    rcases H1 with ⟨U1, ⟨HxU1, ⟨HU1a1U, HU1b1U, HresU1⟩⟩⟩,
    rcases H2 with ⟨U2, ⟨HxU2, ⟨HU2a2U, HU2b2U, HresU2⟩⟩⟩,
    apply quotient.sound,
    use [U1 ∩ U2, ⟨HxU1, HxU2⟩],
    use [set.inter_subset_inter HU1a1U HU2a2U, set.inter_subset_inter HU1b1U HU2b2U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    have HresU1' :
        (F'.res U1 (U1 ∩ U2) (set.inter_subset_left _ _) ((F'.res a1.U U1 HU1a1U) (a1.s))) =
        (F'.res U1 (U1 ∩ U2) (set.inter_subset_left _ _) ((F'.res b1.U U1 HU1b1U) (b1.s)))
    := by rw HresU1,
    have HresU2' :
        (F'.res U2 (U1 ∩ U2) (set.inter_subset_right _ _) ((F'.res a2.U U2 HU2a2U) (a2.s))) =
        (F'.res U2 (U1 ∩ U2) (set.inter_subset_right _ _) ((F'.res b2.U U2 HU2b2U) (b2.s)))
    := by rw HresU2,
    repeat { rw ←(presheaf.Hcomp' F') at HresU1' },
    repeat { rw ←(presheaf.Hcomp' F') at HresU2' },
    repeat { rw ←(presheaf.Hcomp' F') },
    rw [HresU1', HresU2'],
  end }

instance stalk_of_rings_add_semigroup : add_semigroup (stalk_of_rings F x) :=
{ add := stalk_of_rings_has_add.add,
  add_assoc :=
  begin
    intros a b c,
    refine quotient.induction_on₃ a b c _,
    rintros ⟨U, HxU, sU⟩ ⟨V, HxV, sV⟩ ⟨W, HxW, sW⟩,
    have HUVWsub : U ∩ V ∩ W ⊆ U ∩ (V ∩ W)
    := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨HxU, ⟨HxV, HxW⟩⟩,
    apply quotient.sound,
    use [U ∩ V ∩ W, ⟨⟨HxU, HxV⟩, HxW⟩],
    use [set.subset.refl _, HUVWsub],
    dsimp,
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    repeat { erw ←presheaf.Hcomp' },
    rw add_assoc,
  end }

instance stalk_of_rings_add_comm_semigroup : add_comm_semigroup (stalk_of_rings F x) :=
{ add_comm :=
  begin
    intros a b,
    refine quotient.induction_on₂ a b _,
    rintros ⟨U, HxU, sU⟩ ⟨V, HxV, sV⟩,
    apply quotient.sound,
    have HUVUV : U ∩ V ⊆ U ∩ V := λ x HxUV, HxUV,
    have HUVVU : U ∩ V ⊆ V ∩ U := λ x ⟨HxU, HxV⟩, ⟨HxV, HxU⟩,
    use [U ∩ V, ⟨HxU, HxV⟩, HUVUV, HUVVU],
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    repeat { rw ←presheaf.Hcomp' },
    rw add_comm,
  end,
  ..stalk_of_rings_add_semigroup }

-- Zero.

private def stalk_of_rings_zero : stalk_of_rings F x :=
⟦{U := opens.univ, HxU := trivial, s:= 0}⟧

instance stalk_of_rings_has_zero : has_zero (stalk_of_rings F x) :=
{ zero := stalk_of_rings_zero }

instance stalk_of_rings_add_comm_monoid : add_comm_monoid (stalk_of_rings F x) :=
{ zero := stalk_of_rings_zero,
  zero_add :=
  begin
    intros a,
    refine quotient.induction_on a _,
    rintros ⟨U, HxU, sU⟩,
    apply quotient.sound,
    have HUsub : U ⊆ opens.univ ∩ U := λ x HxU, ⟨trivial, HxU⟩,
    use [U, HxU, HUsub, set.subset.refl U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    repeat { rw ←presheaf.Hcomp' },
    erw (is_ring_hom.map_zero ((F.to_presheaf).res _ _ _));
    try { apply_instance },
    rw zero_add,
    refl,
  end,
  add_zero :=
  begin
    intros a,
    refine quotient.induction_on a _,
    rintros ⟨U, HxU, sU⟩,
    apply quotient.sound,
    have HUsub : U ⊆ U ∩ opens.univ := λ x HxU, ⟨HxU, trivial⟩,
    use [U, HxU, HUsub, set.subset.refl U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    repeat { erw ←presheaf.Hcomp' },
    dsimp,
    erw (is_ring_hom.map_zero ((F.to_presheaf).res _ _ _));
    try { apply_instance },
    rw add_zero,
    refl,
  end,
  ..stalk_of_rings_add_comm_semigroup }

-- Neg.

private def stalk_sub_aux :
stalk.elem F.to_presheaf x →
stalk F.to_presheaf x :=
λ s, ⟦{U := s.U, HxU := s.HxU, s := -s.s}⟧

instance stalk_of_rings_has_neg : has_neg (stalk_of_rings F x) :=
{ neg := quotient.lift stalk_sub_aux $
  begin
    intros a b H,
    rcases H with ⟨U, ⟨HxU, ⟨HUaU, HUbU, HresU⟩⟩⟩,
    apply quotient.sound,
    use [U, HxU, HUaU, HUbU],
    repeat { rw @is_ring_hom.map_neg _ _ _ _ _ (F.res_is_ring_hom _ _ _) },
    rw HresU,
  end }

instance stalk_of_rings_add_comm_group : add_comm_group (stalk_of_rings F x) :=
{ neg := stalk_of_rings_has_neg.neg,
  add_left_neg :=
  begin
    intros a,
    refine quotient.induction_on a _,
    rintros ⟨U, HxU, sU⟩,
    apply quotient.sound,
    have HUUU : U ⊆ U ∩ U := λ x HxU, ⟨HxU, HxU⟩,
    have HUuniv : U ⊆ opens.univ := λ x HxU, trivial,
    use [U, HxU, HUUU, HUuniv],
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    repeat { rw ←presheaf.Hcomp' },
    erw (is_ring_hom.map_neg ((F.to_presheaf).res _ _ _));
    try { apply_instance },
    rw add_left_neg,
    erw (is_ring_hom.map_zero ((F.to_presheaf).res _ _ _));
    try { apply_instance },
  end,
  ..stalk_of_rings_add_comm_monoid }

-- Mul.

private def stalk_of_rings_mul_aux :
stalk.elem F.to_presheaf x →
stalk.elem F.to_presheaf x →
stalk F.to_presheaf x :=
λ s t,
⟦{U := s.U ∩ t.U,
HxU := ⟨s.HxU, t.HxU⟩,
s := F.res s.U _ (set.inter_subset_left _ _) s.s *
     F.res t.U _ (set.inter_subset_right _ _) t.s}⟧

instance stalk_of_rings_has_mul : has_mul (stalk_of_rings F x) :=
{ mul := quotient.lift₂ (stalk_of_rings_mul_aux) $
  begin
    intros a1 a2 b1 b2 H1 H2,
    let F' := F.to_presheaf,
    rcases H1 with ⟨U1, ⟨HxU1, ⟨HU1a1U, HU1b1U, HresU1⟩⟩⟩,
    rcases H2 with ⟨U2, ⟨HxU2, ⟨HU2a2U, HU2b2U, HresU2⟩⟩⟩,
    apply quotient.sound,
    use [U1 ∩ U2, ⟨HxU1, HxU2⟩],
    use [set.inter_subset_inter HU1a1U HU2a2U, set.inter_subset_inter HU1b1U HU2b2U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
    have HresU1' :
        (F'.res U1 (U1 ∩ U2) (set.inter_subset_left _ _) ((F'.res a1.U U1 HU1a1U) (a1.s))) =
        (F'.res U1 (U1 ∩ U2) (set.inter_subset_left _ _) ((F'.res b1.U U1 HU1b1U) (b1.s)))
    := by rw HresU1,
    have HresU2' :
        (F'.res U2 (U1 ∩ U2) (set.inter_subset_right _ _) ((F'.res a2.U U2 HU2a2U) (a2.s))) =
        (F'.res U2 (U1 ∩ U2) (set.inter_subset_right _ _) ((F'.res b2.U U2 HU2b2U) (b2.s)))
    := by rw HresU2,
    repeat { rw ←(presheaf.Hcomp' F') at HresU1' },
    repeat { rw ←(presheaf.Hcomp' F') at HresU2' },
    repeat { rw ←(presheaf.Hcomp' F') },
    rw [HresU1', HresU2'],
  end }

instance stalk_of_rings_mul_semigroup : semigroup (stalk_of_rings F x) :=
{ mul := stalk_of_rings_has_mul.mul,
  mul_assoc :=
  begin
    intros a b c,
    refine quotient.induction_on₃ a b c _,
    rintros ⟨U, HxU, sU⟩ ⟨V, HxV, sV⟩ ⟨W, HxW, sW⟩,
    have HUVWsub : U ∩ V ∩ W ⊆ U ∩ (V ∩ W)
    := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨HxU, ⟨HxV, HxW⟩⟩,
    apply quotient.sound,
    use [U ∩ V ∩ W, ⟨⟨HxU, HxV⟩, HxW⟩],
    use [set.subset.refl _, HUVWsub],
    repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
    repeat { rw ←presheaf.Hcomp' },
    rw mul_assoc,
  end }

instance stalk_of_rings_mul_comm_semigroup : comm_semigroup (stalk_of_rings F x) :=
{ mul_comm :=
  begin
    intros a b,
    refine quotient.induction_on₂ a b _,
    rintros ⟨U, HxU, sU⟩ ⟨V, HxV, sV⟩,
    apply quotient.sound,
    have HUVUV : U ∩ V ⊆ U ∩ V := λ x HxUV, HxUV,
    have HUVVU : U ∩ V ⊆ V ∩ U := λ x ⟨HxU, HxV⟩, ⟨HxV, HxU⟩,
    use [U ∩ V, ⟨HxU, HxV⟩, HUVUV, HUVVU],
    repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
    repeat { rw ←presheaf.Hcomp' },
    rw mul_comm,
  end,
  ..stalk_of_rings_mul_semigroup }

-- One.

private def stalk_of_rings_one : stalk_of_rings F x :=
⟦{U := opens.univ, HxU := trivial, s:= 1}⟧

instance stalk_of_rings_has_one : has_one (stalk_of_rings F x) :=
{ one := stalk_of_rings_one }

instance stalk_of_rings_mul_comm_monoid : comm_monoid (stalk_of_rings F x) :=
{ one := stalk_of_rings_one,
  one_mul :=
  begin
    intros a,
    refine quotient.induction_on a _,
    rintros ⟨U, HxU, sU⟩,
    apply quotient.sound,
    have HUsub : U ⊆ opens.univ ∩ U := λ x HxU, ⟨trivial, HxU⟩,
    use [U, HxU, HUsub, set.subset.refl U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
    repeat { rw ←presheaf.Hcomp' },
    erw (is_ring_hom.map_one ((F.to_presheaf).res _ _ _));
    try { apply_instance },
    rw one_mul,
    refl,
  end,
  mul_one :=
  begin
    intros a,
    refine quotient.induction_on a _,
    rintros ⟨U, HxU, sU⟩,
    apply quotient.sound,
    have HUsub : U ⊆ U ∩ opens.univ := λ x HxU, ⟨HxU, trivial⟩,
    use [U, HxU, HUsub, set.subset.refl U],
    repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
    repeat { rw ←presheaf.Hcomp' },
    dsimp,
    erw (is_ring_hom.map_one ((F.to_presheaf).res _ _ _));
    try { apply_instance },
    rw mul_one,
    refl,
  end,
  ..stalk_of_rings_mul_comm_semigroup }

-- Ring.

instance stalk_of_rings_is_comm_ring : comm_ring (stalk_of_rings F x) :=
{ left_distrib :=
  begin
    intros a b c,
    refine quotient.induction_on₃ a b c _,
    rintros ⟨U, HxU, sU⟩ ⟨V, HxV, sV⟩ ⟨W, HxW, sW⟩,
    have HUVWsub : U ∩ V ∩ W ⊆ U ∩ (V ∩ W)
    := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨HxU, ⟨HxV, HxW⟩⟩,
    have HUVWsub2 : U ∩ V ∩ W ⊆ U ∩ V ∩ (U ∩ W)
    := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨⟨HxU, HxV⟩, ⟨HxU, HxW⟩⟩,
    apply quotient.sound,
    use [U ∩ V ∩ W, ⟨⟨HxU, HxV⟩, HxW⟩, HUVWsub, HUVWsub2],
    repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    repeat { rw ←presheaf.Hcomp' },
    repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    repeat { rw ←presheaf.Hcomp' },
    rw mul_add,
  end,
  right_distrib :=
  begin
    intros a b c,
    refine quotient.induction_on₃ a b c _,
    rintros ⟨U, HxU, sU⟩ ⟨V, HxV, sV⟩ ⟨W, HxW, sW⟩,
    have HUVWrfl : U ∩ V ∩ W ⊆ U ∩ V ∩ W := λ x Hx, Hx,
    have HUVWsub : U ∩ V ∩ W ⊆ U ∩ W ∩ (V ∩ W)
    := λ x ⟨⟨HxU, HxV⟩, HxW⟩, ⟨⟨HxU, HxW⟩, ⟨HxV, HxW⟩⟩,
    apply quotient.sound,
    use [U ∩ V ∩ W, ⟨⟨HxU, HxV⟩, HxW⟩, HUVWrfl, HUVWsub],
    repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    repeat { rw ←presheaf.Hcomp' },
    repeat { rw (F.res_is_ring_hom _ _ _).map_mul },
    repeat { rw (F.res_is_ring_hom _ _ _).map_add },
    repeat { rw ←presheaf.Hcomp' },
    rw add_mul,
  end,
  ..stalk_of_rings_add_comm_group,
  ..stalk_of_rings_mul_comm_monoid }

end stalk_of_rings_is_ring

-- Stalks are colimits.

section stalk_colimit

variables {α : Type u} [topological_space α]
variables (F : presheaf_of_rings α) (x : α)

variables (S : Type w) [comm_ring S] [decidable_eq S]
variables (G : Π U, x ∈ U → F.F U → S) [HG : ∀ U, ∀ (h : x ∈ U), is_ring_hom (G U h)]
variables (hg : ∀ U V (H : U ⊆ V) r, ∀ (h : x ∈ U), G U h (F.res V U H r) = G V (H h) r)

def to_stalk (U : opens α) (HxU : x ∈ U) (s : F.F U) : stalk_of_rings F x
:= ⟦{U := U, HxU := HxU, s := s}⟧

instance to_stalk.is_ring_hom (U) (HxU) : is_ring_hom (to_stalk F x U HxU) :=
{ map_one := quotient.sound $ ⟨U, HxU, set.subset.refl _, λ x Hx, trivial,
    begin
        erw (F.res_is_ring_hom _ _ _).map_one,
        erw (F.res_is_ring_hom _ _ _).map_one,
    end⟩,
  map_add := λ y z, quotient.sound $ ⟨U, HxU, set.subset.refl _, λ x Hx, ⟨Hx, Hx⟩,
    begin
        erw ←(F.res_is_ring_hom _ _ _).map_add,
        erw presheaf.Hcomp',
    end⟩,
  map_mul := λ y z, quotient.sound $ ⟨U, HxU, set.subset.refl _, λ x Hx, ⟨Hx, Hx⟩,
    begin
        erw ←(F.res_is_ring_hom _ _ _).map_mul,
        erw presheaf.Hcomp',
    end⟩ }

include hg

protected def to_stalk.rec (y : stalk_of_rings F x) : S :=
quotient.lift_on' y (λ Us, G Us.1 Us.2 Us.3) $
λ ⟨U, HxU, s⟩ ⟨V, HxV, t⟩ ⟨W, HxW, HWU, HWV, Hres⟩,
begin
    dsimp,
    erw [←hg W U HWU s HxW, ←hg W V HWV t HxW, Hres],
end
/-
to_stalk.rec : Π {α : Type u} [_inst_1 : topological_space α] (F : presheaf_of_rings α) (x : α) (S : Type w) [_inst_2 : comm_ring S] [_inst_3 : decidable_eq S] (G : Π (U : opens α), (F.to_presheaf).F U → S), (∀ (U V : opens α) (H : U ⊆ V) (r : (F.to_presheaf).F V), G U ((F.to_presheaf).res V U H r) = G V r) → stalk_of_rings F x → S
-/
theorem to_stalk.rec_to_stalk (U HxU s)
: to_stalk.rec F x S G hg (to_stalk F x U HxU s) = G U HxU s := rfl

include HG

instance to_stalk.rec_is_ring_hom : is_ring_hom (to_stalk.rec F x S G hg) :=
{ map_one := (HG opens.univ (set.mem_univ x)).map_one ▸ rfl,
  map_add := λ y z, quotient.induction_on₂' y z $ λ ⟨U, HxU, s⟩ ⟨V, HxV, t⟩,
    begin
        have HxUV : x ∈ U ∩ V := ⟨HxU, HxV⟩,
        show G (U ∩ V) HxUV (_ + _) = G _ _ _ + G _ _ _,
        rw (HG (U ∩ V) HxUV).map_add,
        erw ←hg (U ∩ V) U (set.inter_subset_left _ _),
        erw ←hg (U ∩ V) V (set.inter_subset_right _ _),
    end,
  map_mul := λ y z, quotient.induction_on₂' y z $ λ ⟨U, HxU, s⟩ ⟨V, HxV, t⟩,
    begin
        have HxUV : x ∈ U ∩ V := ⟨HxU, HxV⟩,
        show G (U ∩ V) HxUV (_ * _) = G _ _ _ * G _ _ _,
        rw (HG (U ∩ V) HxUV).map_mul,
        erw ←hg (U ∩ V) U (set.inter_subset_left _ _),
        erw ←hg (U ∩ V) V (set.inter_subset_right _ _),
    end }

end stalk_colimit

import data.nat.prime
import algebra.group_power
import topology.algebra.ring
import topology.opens

import for_mathlib.prime
import for_mathlib.is_cover
import for_mathlib.sheaves.sheaf_of_topological_rings
import for_mathlib.opens
import for_mathlib.open_embeddings

import continuous_valuations
import r_o_d_completion stalk_valuation
import Huber_pair

universe u

open nat function
open topological_space
open Spa

namespace sheaf_of_topological_rings

instance topological_space {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X)
  (U : opens X) :
  topological_space (𝒪X.F.F U) := presheaf_of_topological_rings.topological_space_sections 𝒪X.F U

instance topological_ring {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X)
  (U : opens X) :
  topological_ring (𝒪X.F.F U) := presheaf_of_topological_rings.Ftop_ring 𝒪X.F U

instance topological_add_group {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X)
  (U : opens X) :
  topological_add_group (𝒪X.F.F U) :=
topological_ring.to_topological_add_group (𝒪X.F.F U)

def uniform_space {X : Type*} [topological_space X] (𝒪X : sheaf_of_topological_rings X)
  (U : opens X) : uniform_space (𝒪X.F.F U) :=
topological_add_group.to_uniform_space (𝒪X.F.F U)

end sheaf_of_topological_rings

section 𝒱
local attribute [instance] sheaf_of_topological_rings.uniform_space

/-- Wedhorn's category 𝒱 -/
structure 𝒱 (X : Type*) [topological_space X] :=
(ℱ : sheaf_of_topological_rings X)
(complete : ∀ U : opens X, complete_space (ℱ.F.F U))
(valuation : ∀ x : X, Spv (stalk_of_rings ℱ.to_presheaf_of_topological_rings.to_presheaf_of_rings x))
(local_stalks : ∀ x : X, is_local_ring (stalk_of_rings ℱ.to_presheaf_of_rings x))
(supp_maximal : ∀ x : X, ideal.is_maximal (_root_.valuation.supp (valuation x).out))

end 𝒱

/-- An auxiliary category 𝒞.  -/
structure 𝒞 (X : Type*) [topological_space X] :=
(F : presheaf_of_topological_rings X)
(valuation: ∀ x : X, Spv (stalk_of_rings F.to_presheaf_of_rings x))

def 𝒱.to_𝒞 {X : Type*} [topological_space X] (ℱ : 𝒱 X) : 𝒞 X :=
{ F := ℱ.ℱ.to_presheaf_of_topological_rings,
  valuation := ℱ.valuation}

noncomputable def 𝒞.Spa (A : Huber_pair) : 𝒞 (Spa A) :=
{ F := Spa.presheaf_of_topological_rings A,
  valuation := λ x, Spv.mk (Spa.presheaf.stalk_valuation x) }

/- Remainder of this file:

morphisms and isomorphisms in 𝒞.
Open set in X -> induced 𝒞 structure
definition of adic space

A morphism in 𝒞 is a map of top spaces, an f-map of presheaves, such that the induced
map on the stalks pulls one valuation back to the other.
-/

instance presheaf_of_rings.comm_ring {X : Type*} [topological_space X]
  (F : presheaf_of_rings X) (U : opens X) : comm_ring (F U) :=
F.Fring U

instance presheaf_of_topological_rings.comm_ring {X : Type*} [topological_space X]
  (F : presheaf_of_topological_rings X) (U : opens X) : comm_ring (F U) :=
F.Fring U

structure presheaf_of_rings.f_map
  {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  (F : presheaf_of_rings X) (G : presheaf_of_rings Y) :=
(f : X → Y)
(hf : continuous f)
(f_flat : ∀ V : opens Y, G V → F (hf.comap V))
(f_flat_is_ring_hom : ∀ V : opens Y, is_ring_hom (f_flat V))
(presheaf_f_flat : ∀ V W : opens Y, ∀ (hWV : W ⊆ V),
  ∀ s : G V, F.res _ _ (hf.comap_mono hWV) (f_flat V s) = f_flat W (G.res V W hWV s))

instance presheaf_of_rings.f_map_flat_is_ring_hom
  {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {F : presheaf_of_rings X} {G : presheaf_of_rings Y}
  (f : presheaf_of_rings.f_map F G) (V : opens Y) :
  is_ring_hom (f.f_flat V) := f.f_flat_is_ring_hom V

def presheaf_of_rings.f_map_id {X : Type*} [topological_space X]
  (F : presheaf_of_rings X) : presheaf_of_rings.f_map F F :=
{ f := λ x, x,
  hf := continuous_id,
  f_flat := λ U, F.res _ _ (λ _ hx, hx),
  f_flat_is_ring_hom := λ U, begin
      convert is_ring_hom.id,
      { simp [continuous.comap_id U] },
      { simp [continuous.comap_id U] },
      { simp [continuous.comap_id U] },
      convert heq_of_eq (F.Hid U),
      swap, exact continuous.comap_id U,
      rw continuous.comap_id U,
      refl,
    end,
  presheaf_f_flat :=  λ U V hVU s, begin
      rw ←F.to_presheaf.Hcomp',
      rw ←F.to_presheaf.Hcomp',
    end }

def presheaf_of_rings.f_map_comp
  {X : Type*} [topological_space X] {Y : Type*} [topological_space Y] {Z : Type*} [topological_space Z]
  {F : presheaf_of_rings X} {G : presheaf_of_rings Y} {H : presheaf_of_rings Z}
  (a : presheaf_of_rings.f_map F G) (b : presheaf_of_rings.f_map G H) : presheaf_of_rings.f_map F H :=
{ f := λ x, b.f (a.f x),
  hf := continuous.comp a.hf b.hf,
  f_flat := λ V s, (a.f_flat (b.hf.comap V)) ((b.f_flat V) s),
  f_flat_is_ring_hom := λ V, show (is_ring_hom ((a.f_flat (b.hf.comap V)) ∘ (b.f_flat V))), from is_ring_hom.comp _ _,
  presheaf_f_flat := λ V W hWV s, begin
    rw ←b.presheaf_f_flat V W hWV s,
    rw ←a.presheaf_f_flat (b.hf.comap V) (b.hf.comap W) (b.hf.comap_mono hWV),
    refl,
  end }

structure presheaf_of_topological_rings.f_map
  {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  (F : presheaf_of_topological_rings X) (G : presheaf_of_topological_rings Y) :=
(f : X → Y)
(hf : continuous f)
(f_flat : ∀ V : opens Y, G V → F (hf.comap V))
[f_flat_is_ring_hom : ∀ V : opens Y, is_ring_hom (f_flat V)]
(cont_f_flat : ∀ V : opens Y, continuous (f_flat V))
(presheaf_f_flat : ∀ V W : opens Y, ∀ (hWV : W ⊆ V),
  ∀ s : G V, F.res _ _ (hf.comap_mono hWV) (f_flat V s) = f_flat W (G.res V W hWV s))

instance presheaf_of_topological_rings.f_map_flat_is_ring_hom
  {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {F : presheaf_of_topological_rings X} {G : presheaf_of_topological_rings Y}
  (f : presheaf_of_topological_rings.f_map F G) (V : opens Y) :
  is_ring_hom (f.f_flat V) := f.f_flat_is_ring_hom V

attribute [instance] presheaf_of_topological_rings.f_map.f_flat_is_ring_hom

def presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map
  {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {F : presheaf_of_topological_rings X} {G : presheaf_of_topological_rings Y}
  (f : presheaf_of_topological_rings.f_map F G) :
  presheaf_of_rings.f_map F.to_presheaf_of_rings G.to_presheaf_of_rings :=
{ ..f}

def presheaf_of_topological_rings.f_map_id
  {X : Type*} [topological_space X]
  {F : presheaf_of_topological_rings X} : presheaf_of_topological_rings.f_map F F :=
{ cont_f_flat := λ U, begin
      show continuous (((F.to_presheaf_of_rings).to_presheaf).res U (continuous.comap continuous_id U) _),
      convert continuous_id,
      { simp [continuous.comap_id U] },
      { simp [continuous.comap_id U] },
      convert heq_of_eq (F.Hid U),
        rw continuous.comap_id U,
      exact continuous.comap_id U,
    end,
  ..presheaf_of_rings.f_map_id F.to_presheaf_of_rings }

def presheaf_of_topological_rings.f_map_comp
  {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {Z : Type*} [topological_space Z] {F : presheaf_of_topological_rings X}
  {G : presheaf_of_topological_rings Y} {H : presheaf_of_topological_rings Z}
  (a : presheaf_of_topological_rings.f_map F G) (b : presheaf_of_topological_rings.f_map G H) :
  presheaf_of_topological_rings.f_map F H :=
{ cont_f_flat := λ V, begin
    show continuous
    ((a.f_flat (b.hf.comap V)) ∘
         (b.f_flat V)),
    apply continuous.comp,
      apply b.cont_f_flat,
    apply a.cont_f_flat
  end,
  ..presheaf_of_rings.f_map_comp a.to_presheaf_of_rings_f_map b.to_presheaf_of_rings_f_map }
-- need a construction `stalk_map` attached to an f-map; should follow from UMP
-- Need this before we embark on 𝒞.map

local attribute [instance, priority 0] classical.prop_decidable

/-- The map on stalks induced from an f-map -/
noncomputable def stalk_map {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {F : presheaf_of_rings X} {G : presheaf_of_rings Y} (f : presheaf_of_rings.f_map F G)
  (x : X) : stalk_of_rings G (f.f x) → stalk_of_rings F x :=
to_stalk.rec G (f.f x) (stalk_of_rings F x)
  (λ V hfx s, ⟦⟨f.hf.comap V, hfx, f.f_flat V s⟩⟧)
  (λ V W H r hfx, quotient.sound begin
    use [f.hf.comap V, hfx, set.subset.refl _, f.hf.comap_mono H],
    erw F.to_presheaf.Hid,
    symmetry,
    apply f.presheaf_f_flat
  end )

instance {X : Type*} [topological_space X] {F : presheaf_of_rings X} (x : X) :
  comm_ring (quotient (stalk.setoid (F.to_presheaf) x)) :=
stalk_of_rings_is_comm_ring F x

instance f_flat_is_ring_hom {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {F : presheaf_of_rings X} {G : presheaf_of_rings Y} (f : presheaf_of_rings.f_map F G)
  (x : X) (V : opens Y) (hfx : f.f x ∈ V) :
  is_ring_hom (λ (s : G.F V), (⟦⟨f.hf.comap V, hfx, f.f_flat V s⟩⟧ : stalk_of_rings F x)) :=
begin
  show is_ring_hom ((to_stalk F x (f.hf.comap V) hfx) ∘ (f.f_flat V)),
  refine is_ring_hom.comp _ _,
end

instance {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {F : presheaf_of_rings X} {G : presheaf_of_rings Y} (f : presheaf_of_rings.f_map F G)
  (x : X) : is_ring_hom (stalk_map f x) := to_stalk.rec_is_ring_hom _ _ _ _ _

lemma stalk_map_id {X : Type*} [topological_space X]
  (F : presheaf_of_rings X) (x : X) (s : stalk_of_rings F x) :
  stalk_map (presheaf_of_rings.f_map_id F) x s = s :=
begin
  induction s,
    apply quotient.sound,
    use s.U,
    use s.HxU,
    use (le_refl s.U),
    use (le_refl s.U),
    symmetry,
    convert (F.to_presheaf.Hcomp' _ _ _ _ _ s.s),
  refl,
end

lemma stalk_map_id' {X : Type*} [topological_space X]
  (F : presheaf_of_rings X) (x : X) :
  stalk_map (presheaf_of_rings.f_map_id F) x = id := by ext; apply stalk_map_id

lemma stalk_map_comp {X : Type*} [topological_space X]
  {Y : Type*} [topological_space Y] {Z : Type*} [topological_space Z]
   {F : presheaf_of_rings X}
  {G : presheaf_of_rings Y} {H : presheaf_of_rings Z}
  (a : presheaf_of_rings.f_map F G) (b : presheaf_of_rings.f_map G H) (x : X)
  (s : stalk_of_rings H (b.f (a.f x))) :
  stalk_map (presheaf_of_rings.f_map_comp a b) x s =
  stalk_map a x (stalk_map b (a.f x) s) :=
begin
  induction s,
    apply quotient.sound,
    use a.hf.comap (b.hf.comap s.U),
    use s.HxU,
    existsi _, swap, intros t ht, exact ht,
    existsi _, swap, intros t ht, exact ht,
    refl,
  refl,
end


lemma stalk_map_comp' {X : Type*} [topological_space X]
  {Y : Type*} [topological_space Y] {Z : Type*} [topological_space Z]
  {F : presheaf_of_rings X}
  {G : presheaf_of_rings Y} {H : presheaf_of_rings Z}
  (a : presheaf_of_rings.f_map F G) (b : presheaf_of_rings.f_map G H) (x : X) :
  stalk_map (presheaf_of_rings.f_map_comp a b) x =
  (stalk_map a x) ∘ (stalk_map b (a.f x)) := by ext; apply stalk_map_comp

structure 𝒞.map {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  (F : 𝒞 X) (G : 𝒞 Y) :=
(fmap : presheaf_of_topological_rings.f_map F.F G.F)
(stalk : ∀ x : X, ((F.valuation x).out.comap (stalk_map fmap.to_presheaf_of_rings_f_map x)).is_equiv
  (G.valuation (fmap.f x)).out)

/- this is to check that equality of maps is what you think it is; we don't need this though.
def 𝒞.map_ext_aux {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {F : 𝒞 X} {G : 𝒞 Y} {a b : 𝒞.map F G} (hf : a.fmap.f = b.fmap.f) (V : opens Y) : a.fmap.hf.comap V ⊆ b.fmap.hf.comap V :=
begin
  show a.fmap.f ⁻¹' V ⊆ b.fmap.f ⁻¹' V,
  rw hf
end

def 𝒞.map_ext {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {F : 𝒞 X} {G : 𝒞 Y} (a b : 𝒞.map F G) (hf : a.fmap.f = b.fmap.f)
  (hflat : ∀ V : opens Y, ∀ s : G.F V,
    a.fmap.f_flat V s = F.F.res _ _ (𝒞.map_ext_aux hf V) (b.fmap.f_flat V s)) : a = b :=
begin
  cases a with amap ast, cases b with bmap bst,
  congr,
  cases amap, cases bmap,
  dsimp at hf,
  cases hf,
  congr,
  funext V s,
  dsimp at hflat,
  convert hflat V s,
  have Hid' : bmap_f_flat V s =
      (((F.F).to_presheaf_of_rings).to_presheaf).res (continuous.comap bmap_hf V) (continuous.comap bmap_hf V) _
        (bmap_f_flat V s),
    rw F.F.Hid, refl,
  convert Hid'
end
-/

-- getting sick of these crappy proofs
def 𝒞.map_id {X : Type*} [topological_space X] (F : 𝒞 X) : 𝒞.map F F :=
{ fmap := presheaf_of_topological_rings.f_map_id,
  stalk := λ x, begin
    show valuation.is_equiv
    (valuation.comap (Spv.out (F.valuation x))
       (stalk_map
          (presheaf_of_rings.f_map_id F.F.to_presheaf_of_rings)
          x))
    (Spv.out (F.valuation ((λ (x : X), x) x))),
    simp [stalk_map_id' F.F.to_presheaf_of_rings x],
    convert valuation.is_equiv.refl,
    unfold valuation.comap,
    dsimp,
    unfold_coes,
    rw subtype.ext,
  end }

def 𝒞.map_comp {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  {Z : Type*} [topological_space Z] {F : 𝒞 X} {G : 𝒞 Y} {H : 𝒞 Z}
  (a : 𝒞.map F G) (b : 𝒞.map G H) : 𝒞.map F H :=
{ fmap := presheaf_of_topological_rings.f_map_comp a.fmap b.fmap,
  stalk := λ x, begin refine valuation.is_equiv.trans _ (b.stalk (a.fmap.f x)),
    let XXX := a.stalk x,
    let YYY := valuation.is_equiv.comap (stalk_map (presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map (b.fmap))
          ((presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map (a.fmap)).f x)) XXX,
    show valuation.is_equiv _ (valuation.comap (Spv.out (G.valuation ((a.fmap).f x))) _),
    refine valuation.is_equiv.trans _ YYY,
    rw ←valuation.comap_comp,
    suffices : (stalk_map
          (presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map
             (presheaf_of_topological_rings.f_map_comp (a.fmap) (b.fmap)))
          x) = (stalk_map (presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map (a.fmap)) x ∘
          stalk_map (presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map (b.fmap))
            ((presheaf_of_topological_rings.f_map.to_presheaf_of_rings_f_map (a.fmap)).f x)),
      simp [this],
    rw ←stalk_map_comp',
    refl,
  end }

structure 𝒞.equiv {X : Type*} [topological_space X] {Y : Type*} [topological_space Y]
  (F : 𝒞 X) (G : 𝒞 Y) :=
(to_fun : 𝒞.map F G)
(inv_fun : 𝒞.map G F)
(left_inv : 𝒞.map_comp to_fun inv_fun = 𝒞.map_id F)
(right_inv : 𝒞.map_comp inv_fun to_fun = 𝒞.map_id G)

notation A ` ≅_𝒞 `:50 B := nonempty (𝒞.equiv A B)

def presheaf_of_rings.restrict {X : Type*} [topological_space X] (U : opens X)
  (G : presheaf_of_rings X) : presheaf_of_rings U :=
  { F := λ V, G.F (topological_space.opens.map U V),
    res := λ V W HWV, G.res _ _ (topological_space.opens.map_mono HWV),
    Hid := λ V, G.Hid (topological_space.opens.map U V),
    Hcomp := λ V₁ V₂ V₃ H12 H23, G.Hcomp (topological_space.opens.map U V₁)
      (topological_space.opens.map U V₂) (topological_space.opens.map U V₃)
      (topological_space.opens.map_mono H12) (topological_space.opens.map_mono H23),
    Fring := λ V, G.Fring (topological_space.opens.map U V),
    res_is_ring_hom := λ V W HWV, G.res_is_ring_hom (topological_space.opens.map U V)
      (topological_space.opens.map U W) (topological_space.opens.map_mono HWV) }

noncomputable def presheaf_of_rings.restrict_stalk_map {X : Type*} [topological_space X]
  {U : opens X} (G : presheaf_of_rings X) (u : U) :
  stalk_of_rings (presheaf_of_rings.restrict U G) u → stalk_of_rings G u :=
to_stalk.rec (presheaf_of_rings.restrict U G) u (stalk_of_rings G u)
  (λ V hu, to_stalk G u (topological_space.opens.map U V) ( opens.map_mem_of_mem hu))
  (λ W V HWV s huW, quotient.sound (begin
    use [(topological_space.opens.map U W), opens.map_mem_of_mem huW],
    use [(set.subset.refl (topological_space.opens.map U W)), topological_space.opens.map_mono HWV],
    rw G.Hid (topological_space.opens.map U W),
    refl,
  end))

instance {X : Type*} [topological_space X] {U : opens X} (G : presheaf_of_rings X) (u : U) :
  is_ring_hom (presheaf_of_rings.restrict_stalk_map G u) :=
by unfold presheaf_of_rings.restrict_stalk_map; apply_instance

def presheaf_of_topological_rings.restrict {X : Type*} [topological_space X] (U : opens X)
  (G : presheaf_of_topological_rings X) : presheaf_of_topological_rings U :=
  { Ftop := λ V, G.Ftop (topological_space.opens.map U V),
    Ftop_ring := λ V, G.Ftop_ring (topological_space.opens.map U V),
    res_continuous := λ V W HWV, G.res_continuous (topological_space.opens.map U V)
      (topological_space.opens.map U W) (topological_space.opens.map_mono HWV),
  ..presheaf_of_rings.restrict U G.to_presheaf_of_rings }

noncomputable def 𝒞.restrict {X : Type*} [topological_space X] (U : opens X) (G : 𝒞 X) : 𝒞 U :=
{ F := presheaf_of_topological_rings.restrict U G.F,
  valuation :=
    λ u, Spv.mk (valuation.comap (G.valuation u).out (presheaf_of_rings.restrict_stalk_map _ _)) }

structure adic_space (X : Type u) [topological_space X] :=
(locally_ringed_valued_space : 𝒱 X)
(Hlocally_affinoid : ∃ (I : Type u) (U : I → opens X) (Hcover : set.Union (λ i, (U i).1) = set.univ)
  (R : I → Huber_pair),
  ∀ i : I, nonempty (𝒞.equiv (𝒞.Spa (R i)) (𝒞.restrict (U i) locally_ringed_valued_space.to_𝒞)))

-- note that currently we can't even prove that Spa(A) is a pre-adic space,
-- because we don't know that the rational opens are a basis. I didn't
-- even bother defining a pre-adic space -- one would have to define 𝒱^{pre}
-- which is 𝒱 with the sheaf axiom dropped.

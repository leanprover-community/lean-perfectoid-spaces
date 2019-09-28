import for_mathlib.open_embeddings

import sheaves.sheaf_of_topological_rings
import sheaves.stalk_of_rings

universe variable u

open topological_space

variables {X : Type u} {Y : Type u} {Z : Type u}
variables [topological_space X] [topological_space Y] [topological_space Z]

namespace presheaf_of_rings
variables {F : presheaf_of_rings X} {G : presheaf_of_rings Y} {H : presheaf_of_rings Z}

structure f_map
  (F : presheaf_of_rings X) (G : presheaf_of_rings Y) :=
(f : X → Y)
(hf : continuous f)
(f_flat : ∀ V : opens Y, G V → F (hf.comap V))
(f_flat_is_ring_hom : ∀ V : opens Y, is_ring_hom (f_flat V))
(presheaf_f_flat : ∀ V W : opens Y, ∀ (hWV : W ⊆ V),
  ∀ s : G V, F.res _ _ (hf.comap_mono hWV) (f_flat V s) = f_flat W (G.res V W hWV s))

instance f_map_flat.is_ring_hom (f : presheaf_of_rings.f_map F G) (V : opens Y) :
  is_ring_hom (f.f_flat V) := f.f_flat_is_ring_hom V

def f_map_id (F : presheaf_of_rings X) : presheaf_of_rings.f_map F F :=
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

def f_map.comp (a : presheaf_of_rings.f_map F G) (b : presheaf_of_rings.f_map G H) :
presheaf_of_rings.f_map F H :=
{ f := λ x, b.f (a.f x),
  hf := b.hf.comp a.hf,
  f_flat := λ V s, (a.f_flat (b.hf.comap V)) ((b.f_flat V) s),
  f_flat_is_ring_hom := λ V, show (is_ring_hom ((a.f_flat (b.hf.comap V)) ∘ (b.f_flat V))), from is_ring_hom.comp _ _,
  presheaf_f_flat := λ V W hWV s,
  begin
    rw ←b.presheaf_f_flat V W hWV s,
    rw ←a.presheaf_f_flat (b.hf.comap V) (b.hf.comap W) (b.hf.comap_mono hWV),
    refl,
  end }

@[simp] lemma f_map.id_comp (a : presheaf_of_rings.f_map F G) :
  (presheaf_of_rings.f_map_id F).comp a = a :=
begin
  cases a, delta presheaf_of_rings.f_map_id presheaf_of_rings.f_map.comp,
  congr, funext V s, dsimp,
  show _ = id _, apply congr_fun, exact F.to_presheaf.Hid _,
end

@[simp] lemma f_map.comp_id (a : presheaf_of_rings.f_map F G) :
  a.comp (presheaf_of_rings.f_map_id G) = a :=
begin
  cases a with f hf f_flat f_flat_is_ring_hom presheaf_f_flat,
  delta presheaf_of_rings.f_map_id presheaf_of_rings.f_map.comp,
  congr, funext V s, dsimp,
  rw ← presheaf_f_flat,
  show _ = id _, apply congr_fun, exact F.to_presheaf.Hid _,
end

end presheaf_of_rings

namespace presheaf_of_topological_rings
variables {F : presheaf_of_topological_rings X} {G : presheaf_of_topological_rings Y} {H : presheaf_of_topological_rings Z}

structure f_map (F : presheaf_of_topological_rings X) (G : presheaf_of_topological_rings Y) :=
(f : X → Y)
(hf : continuous f)
(f_flat : ∀ V : opens Y, G V → F (hf.comap V))
[f_flat_is_ring_hom : ∀ V : opens Y, is_ring_hom (f_flat V)]
(cont_f_flat : ∀ V : opens Y, continuous (f_flat V))
(presheaf_f_flat : ∀ V W : opens Y, ∀ (hWV : W ⊆ V),
  ∀ s : G V, F.res _ _ (hf.comap_mono hWV) (f_flat V s) = f_flat W (G.res V W hWV s))

instance f_map_flat.is_ring_hom (f : presheaf_of_topological_rings.f_map F G) (V : opens Y) :
  is_ring_hom (f.f_flat V) := f.f_flat_is_ring_hom V

attribute [instance] presheaf_of_topological_rings.f_map.f_flat_is_ring_hom

def f_map.to_presheaf_of_rings_f_map
  {X : Type u} [topological_space X] {Y : Type u} [topological_space Y]
  {F : presheaf_of_topological_rings X} {G : presheaf_of_topological_rings Y}
  (f : presheaf_of_topological_rings.f_map F G) :
  presheaf_of_rings.f_map F.to_presheaf_of_rings G.to_presheaf_of_rings :=
{ ..f}

@[extensionality]
lemma presheaf_of_topological_rings.f_map.ext
  {X : Type u} [topological_space X] {Y : Type u} [topological_space Y]
  {F : presheaf_of_topological_rings X} {G : presheaf_of_topological_rings Y}
  (a b : F.f_map G) (h : a.to_presheaf_of_rings_f_map = b.to_presheaf_of_rings_f_map) :
  a = b :=
begin
  cases a, cases b,
  dsimp [f_map.to_presheaf_of_rings_f_map] at h,
  injections,
  simp [*]
end

@[simp] lemma f_map.to_presheaf_of_rings_f_map_f (f : presheaf_of_topological_rings.f_map F G) :
  f.to_presheaf_of_rings_f_map.f = f.f := rfl

def f_map_id (F : presheaf_of_topological_rings X) :
  presheaf_of_topological_rings.f_map F F :=
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

@[simp] lemma f_map.to_presheaf_of_rings_f_map_id (F : presheaf_of_topological_rings X) :
  (presheaf_of_topological_rings.f_map_id F).to_presheaf_of_rings_f_map =
  presheaf_of_rings.f_map_id F.to_presheaf_of_rings := rfl

@[simp] lemma f_map_id_apply (F : presheaf_of_topological_rings X) (x : X) :
  (presheaf_of_topological_rings.f_map_id F).f x = x := rfl

def f_map.comp (a : presheaf_of_topological_rings.f_map F G) (b : presheaf_of_topological_rings.f_map G H) :
  presheaf_of_topological_rings.f_map F H :=
{ cont_f_flat := λ V, (a.cont_f_flat _).comp (b.cont_f_flat _),
  .. a.to_presheaf_of_rings_f_map.comp b.to_presheaf_of_rings_f_map }

@[simp] lemma f_map.comp_f (a : presheaf_of_topological_rings.f_map F G) (b : presheaf_of_topological_rings.f_map G H) :
  (a.comp b).f = b.f ∘ a.f := rfl

@[simp] lemma f_map.comp_to_presheaf_of_rings_f_map
  (a : presheaf_of_topological_rings.f_map F G) (b : presheaf_of_topological_rings.f_map G H) :
  (a.comp b).to_presheaf_of_rings_f_map =
  a.to_presheaf_of_rings_f_map.comp b.to_presheaf_of_rings_f_map := rfl

@[simp] lemma f_map.id_comp (a : presheaf_of_topological_rings.f_map F G) :
  (presheaf_of_topological_rings.f_map_id F).comp a = a :=
by ext; simp

@[simp] lemma f_map.comp_id (a : presheaf_of_topological_rings.f_map F G) :
  a.comp (presheaf_of_topological_rings.f_map_id G) = a :=
by ext; simp

end presheaf_of_topological_rings

open_locale classical

/-- The map on stalks induced from an f-map -/
noncomputable def stalk_map {F : presheaf_of_rings X} {G : presheaf_of_rings Y}
  (f : F.f_map G) (x : X) :
  stalk_of_rings G (f.f x) → stalk_of_rings F x :=
to_stalk.rec G (f.f x) (stalk_of_rings F x)
  (λ V hfx s, ⟦⟨f.hf.comap V, hfx, f.f_flat V s⟩⟧)
  (λ V W H r hfx, quotient.sound begin
    use [f.hf.comap V, hfx, set.subset.refl _, f.hf.comap_mono H],
    erw F.to_presheaf.Hid,
    symmetry,
    apply f.presheaf_f_flat
  end )

namespace stalk_map
variables {F : presheaf_of_rings X} {G : presheaf_of_rings Y} {H : presheaf_of_rings Z}
variables (f : F.f_map G) (g : G.f_map H)

instance (F : presheaf_of_rings X) (x : X) :
  comm_ring (quotient (stalk.setoid (F.to_presheaf) x)) :=
stalk_of_rings_is_comm_ring F x

instance f_flat_is_ring_hom (x : X) (V : opens Y) (hfx : f.f x ∈ V) :
  is_ring_hom (λ (s : G.F V), (⟦⟨f.hf.comap V, hfx, f.f_flat V s⟩⟧ : stalk_of_rings F x)) :=
begin
  show is_ring_hom ((to_stalk F x (f.hf.comap V) hfx) ∘ (f.f_flat V)),
  refine is_ring_hom.comp _ _,
end

instance (x : X) : is_ring_hom (stalk_map f x) := to_stalk.rec_is_ring_hom _ _ _ _ _

@[simp] lemma stalk_map_id (F : presheaf_of_rings X) (x : X) (s : stalk_of_rings F x) :
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

@[simp] lemma stalk_map_id' (F : presheaf_of_rings X) (x : X) :
  stalk_map (presheaf_of_rings.f_map_id F) x = id := by ext; apply stalk_map_id

lemma stalk_map_comp (x : X) (s : stalk_of_rings H (g.f (f.f x))) :
  stalk_map (f.comp g) x s = stalk_map f x (stalk_map g (f.f x) s) :=
begin
  induction s,
    apply quotient.sound,
    use f.hf.comap (g.hf.comap s.U),
    use s.HxU,
    existsi _, swap, intros t ht, exact ht,
    existsi _, swap, intros t ht, exact ht,
    refl,
  refl,
end

@[simp] lemma stalk_map_comp' (x : X) :
  stalk_map (f.comp g) x = (stalk_map f x) ∘ (stalk_map g (f.f x)) :=
by ext; apply stalk_map_comp

end stalk_map

namespace presheaf_of_rings

def restrict (U : opens X) (G : presheaf_of_rings X) :
  presheaf_of_rings U :=
{ F := λ V, G.F (topological_space.opens.map U V),
  res := λ V W HWV, G.res _ _ (topological_space.opens.map_mono HWV),
  Hid := λ V, G.Hid (topological_space.opens.map U V),
  Hcomp := λ V₁ V₂ V₃ H12 H23, G.Hcomp (topological_space.opens.map U V₁)
    (topological_space.opens.map U V₂) (topological_space.opens.map U V₃)
    (topological_space.opens.map_mono H12) (topological_space.opens.map_mono H23),
  Fring := λ V, G.Fring (topological_space.opens.map U V),
  res_is_ring_hom := λ V W HWV, G.res_is_ring_hom (topological_space.opens.map U V)
    (topological_space.opens.map U W) (topological_space.opens.map_mono HWV) }

variables {U : opens X} (G : presheaf_of_rings X) (u : U)

noncomputable def restrict_stalk_map :
  stalk_of_rings (G.restrict U) u → stalk_of_rings G u :=
to_stalk.rec (G.restrict U) u (stalk_of_rings G u)
  (λ V hu, to_stalk G u (topological_space.opens.map U V) ( opens.map_mem_of_mem hu))
  (λ W V HWV s huW, quotient.sound (begin
    use [(topological_space.opens.map U W), opens.map_mem_of_mem huW],
    use [(set.subset.refl (topological_space.opens.map U W)), topological_space.opens.map_mono HWV],
    rw G.Hid (topological_space.opens.map U W),
    refl,
  end))

instance : is_ring_hom (G.restrict_stalk_map u) :=
by delta restrict_stalk_map; apply_instance

end presheaf_of_rings

def presheaf_of_topological_rings.restrict  (U : opens X) (G : presheaf_of_topological_rings X) :
  presheaf_of_topological_rings U :=
{ Ftop := λ V, G.Ftop (topological_space.opens.map U V),
  Ftop_ring := λ V, G.Ftop_ring (topological_space.opens.map U V),
  res_continuous := λ V W HWV, G.res_continuous (topological_space.opens.map U V)
    (topological_space.opens.map U W) (topological_space.opens.map_mono HWV),
..presheaf_of_rings.restrict U G.to_presheaf_of_rings }

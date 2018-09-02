import for_mathlib.topological_structures
import for_mathlib.completion

universe u
variables {α : Type*} [uniform_space α]
variables (G : Type u) [add_comm_group G] [topological_space G] [topological_add_group G]  

open uniform_space function set uniform_space.to_completion

lemma uniform_continuous_add'' [add_group α] [uniform_add_group α] : 
  uniform_continuous (uncurry (+) : α × α → α) :=
by rw uncurry_def ; exact uniform_continuous_add'

noncomputable
def uncurry_add : completion G × completion G → completion G := completion.map₂ (+)


noncomputable instance completion_add : has_add (completion G) := ⟨curry (uncurry_add G)⟩

instance completion_zero : has_zero (completion G) := ⟨(0:G)⟩

noncomputable instance completion_neg : has_neg (completion G) := ⟨completion.map (λ x, -x)⟩

variable {G}
lemma completion.add_lift (a b : G) : (a : completion G) + (b : completion G) = (a + b : G) := 
by simpa only [completion.map.lifts₂' uniform_continuous_add'']

lemma completion.neg_lift (a : G) : -(a : completion G) = (-a : G) := 
by simpa only [completion.map.lifts' uniform_continuous_neg']

lemma completion.uniform_continuous_add' : uniform_continuous (uncurry_add G) := 
completion.map.uniform_continuity₂ uniform_continuous_add''

lemma completion.uniform_continuous_add {f g : α → completion G} (hf : uniform_continuous f) (hg : uniform_continuous g) : uniform_continuous (λ x, f x + g x) := 
uniform_continuous.comp (uniform_continuous.prod_mk hf hg) completion.uniform_continuous_add'

lemma completion.continuous_add' : continuous (uncurry_add G) := 
uniform_continuous.continuous completion.uniform_continuous_add'

lemma completion.continuous_add'' : continuous (λ x : (completion G) × (completion G), x.1 + x.2) :=
begin
  change continuous (λ (x : (completion G) × (completion G)), (uncurry_add G) (x.fst, x.snd)),
  simp[completion.continuous_add']
end 
      

lemma completion.continuous_add {f g : α → completion G} (hf : continuous f) (hg : continuous g) : continuous (λ x, f x + g x) := 
continuous.comp (continuous.prod_mk hf hg) completion.continuous_add'

lemma completion.uniform_continuous_neg' : uniform_continuous (λ x : completion G, -x) := 
completion.map.uniform_continuity uniform_continuous_neg'

lemma completion.uniform_continuous_neg {f : α → completion G} (hf : uniform_continuous f) : uniform_continuous (λ x, -f x) := 
uniform_continuous.comp hf completion.uniform_continuous_neg'

lemma completion.continuous_neg' : continuous (λ x : completion G, -x) := 
uniform_continuous.continuous completion.uniform_continuous_neg'

lemma completion.continuous_neg {f : α → completion G} (hf : continuous f) : continuous (λ x, -f x) := 
continuous.comp hf completion.continuous_neg'

noncomputable
instance completion_group_str : add_comm_group (completion G) := 
begin
  let H := completion G,
  refine_struct { .. completion_add G, ..completion_zero G, ..completion_neg G, .. },
  { intros a b c,
    have closed : is_closed {x : H × H × H | x.1 + x.2.1 + x.2.2 = x.1 + (x.2.1 + x.2.2) }, 
    { 
      have c₁ : continuous (λ x : H × (H × H), (x.1 + x.2.1) + x.2.2), 
      { have c : continuous (λ x : H × (H × H), (x.2.1 + x.2.2) + x.1) :=
          completion.continuous_add (continuous.comp continuous_snd completion.continuous_add'') continuous_fst,
        exact continuous.comp continuous_pat_perm c },
      have c₂ : continuous (λ x : H × (H × H), x.1 + (x.2.1 + x.2.2)) := 
        completion.continuous_add continuous_fst (continuous.comp continuous_snd completion.continuous_add''),
      exact is_closed_eq c₁ c₂ },
    have := is_closed_property dense₃ closed (by {intro a, repeat { rw completion.add_lift }, rw add_assoc }),
    exact this ⟨a, b, c⟩ },
  { have closed : is_closed {x : H | 0 + x = x } := 
      is_closed_eq (completion.continuous_add continuous_const continuous_id) continuous_id,
    exact is_closed_property dense₁ closed (by {intro x, change ((0:G):completion G) + x = x, rw completion.add_lift, rw zero_add}) },
  { have closed : is_closed {x : H | x + (0:G) = x } :=
      is_closed_eq (completion.continuous_add continuous_id continuous_const) continuous_id ,
    exact is_closed_property dense₁ closed (by {intro x, change (x :completion G) + ((0:G):completion G) = x, rw completion.add_lift, rw add_zero}) },
  { have closed : is_closed {x : H | -x + x = (0:G)} :=
     is_closed_eq (completion.continuous_add completion.continuous_neg' continuous_id) continuous_const,
    have := is_closed_property dense₁ closed (by {intro x, rw completion.neg_lift, rw completion.add_lift, rw add_left_neg }),
    exact this },
  { intros a b,
    have closed : is_closed {x : H × H | x.1 + x.2 = x.2 + x.1 } :=
      is_closed_eq completion.continuous_add'' (continuous.comp continuous_swap completion.continuous_add''),
    have := is_closed_property dense₂ closed (by {intro a, repeat { rw completion.add_lift }, rw add_comm }),
    exact this ⟨a, b⟩ },
end

-- The following two instances seem to be necessary to short-circuit what would otherwise be class instance resolution loops
instance completion_top_space : topological_space (completion G) := by unfold completion ; apply_instance
instance completion_prod_top : topological_space ((completion G) × (completion G)) := by unfold completion ; apply_instance

instance completion_group_top : topological_add_group (completion G) := 
begin
  refine {..}, -- no idea why I cannot directly construct this instance
  { exact completion.continuous_add'' },
  { exact completion.continuous_neg' }
end


instance to_completion_mph : is_add_group_hom (to_completion G) := 
⟨begin
  intros a b,
  change ↑(a + b)= ↑a + ↑b,
  exact eq.symm (completion.add_lift a b)
end⟩

variables {H : Type u} [add_comm_group H] [topological_space H] [topological_add_group H] 

/-- The following would be really good to know. Hopefully it would allow to unsorry completion_map_hom below -/
lemma same_uniformity : uniform_space.completion_uniform_space H = topological_add_group.to_uniform_space (completion H) :=
begin
  apply uniform_space_eq,
  dsimp[uniform_space.completion_uniform_space, topological_add_group.to_uniform_space, completion ],
    
  sorry
end

instance completion_extension_hom [complete_space H] [separated H] 
  {f : G → H} [is_add_group_hom f] (h : continuous f) : 
  is_add_group_hom (completion_extension f) :=
⟨begin
  
  let GG := completion G,
  let ff := completion_extension f,
  have f_uc := uniform_continuous_of_continuous h,
  have ff_c : continuous ff := completion_extension.continuity f_uc,
    
  have closed : is_closed {x : GG × GG | ff (x.1 + x.2) = ff x.1 + ff x.2 },
  { have c₀ : continuous (λ x : GG × GG, x.1 + x.2), 
      { change continuous (λ (x : GG × GG), (uncurry_add G) (x.fst, x.snd)),
        simp[completion.continuous_add'] },
    
    have c₁ : continuous (λ a : GG × GG, ff a.1) := continuous.comp continuous_fst ff_c,
    have c₂ : continuous (λ a : GG × GG, ff a.2) := continuous.comp continuous_snd ff_c,
    
    haveI t2 : t2_space H := separated_t2, -- No idea why this is needed
    exact is_closed_eq  (continuous.comp c₀ ff_c) (continuous_add c₁ c₂) },
  have eq_on_G : ∀ (a : G × G), ff (a.1 +  a.2) = ff a.1 + ff a.2,
  { rintro ⟨a, b⟩,
      dsimp[ff],
      rw completion.add_lift,
      repeat { rw ←completion_extension.lifts' f_uc },
      rw is_add_group_hom.add f },
    
  have := is_closed_property dense₂ closed eq_on_G,
  
  exact λ a b, this (a, b),
end⟩

instance completion_map_hom {f : G → H} [is_add_group_hom f] (h : continuous f) :
  is_add_group_hom (completion.map f) :=
begin
  dsimp [completion.map],
  have cont : continuous (to_completion H ∘ f) := continuous.comp h (to_completion.continuous H),
  have hom : is_add_group_hom (to_completion H ∘ f), apply_instance,
  haveI complete : complete_space (completion H) := sorry, 
  -- apply_instance doesn't work above because the uniform space structure used by Lean comes 
  -- from the group structure, not from the completion
  haveI sep : separated (completion H) := sorry, -- same comment
  
  have := completion_extension_hom cont,
  sorry -- `exact this` doesn't work, because of the instance nightmare above
end
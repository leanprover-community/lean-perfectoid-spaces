import logic.basic

theorem forall_iff_forall_surj {α β : Type*} {f : α → β} (h : function.surjective f) {P : β → Prop} :
(∀ a, P (f a)) ↔ ∀ b, P b:=
⟨λ ha b, by cases h b with a hab; rw ←hab; exact ha a, λ hb a, hb $ f a⟩

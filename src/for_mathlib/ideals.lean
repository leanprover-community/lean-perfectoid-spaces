import ring_theory.ideals

theorem is_ideal.add {R : Type*} [comm_ring R] {E : set R} [is_ideal E] {x y : R}
  (Hx : x ∈ E) (Hy : y ∈ E) : x + y ∈ E :=
is_submodule.add Hx Hy

theorem is_ideal.zero {R : Type*} [comm_ring R] {E : set R} [is_ideal E] : (0 : R) ∈ E :=
is_submodule.zero_ R E

theorem is_ideal.mul_left {R : Type*} [comm_ring R] {E : set R} [is_ideal E] (c : R) {x : R}
  (H : x ∈ E) : c * x ∈ E :=
is_submodule.smul c H

theorem is_ideal.mul_right {R : Type*} [comm_ring R] {E : set R} [is_ideal E] {x : R} (c : R)
  (H : x ∈ E) : x * c ∈ E :=
mul_comm c x ▸ is_ideal.mul_left c H

theorem is_proper_ideal.one_not_mem {α : Type*} [comm_ring α] {S : set α} [is_proper_ideal S] : (1:α) ∉ S :=
λ h, is_proper_ideal.ne_univ S $ is_submodule.univ_of_one_mem S h

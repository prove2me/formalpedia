-- Prove2me | solution 1 for mme_released_interior_child_boundary_or_canonical_112
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T04:41:56.673682+00:00
-- url     : https://prove2.me/submissions/34947925-764e-4f24-9d83-0b046b429991

import Definitions.Def_mme_released_interior_integer_profiles

open MME MME.RecursiveYZ MME.ReleasedInterior

/-- A square child is either a boundary shape or one of the three coordinate
placements of 112. This depends only on its total grade, not on the recipe. -/
theorem mme_square_child_boundary_or_permuted_112
    {p : Fin 3 → ℕ} (c : RecursiveThinSplit.Split 4 p) :
    (∃ i : Fin 3, (c.val i).val = 0) ∨
    ((c.val 0).val = 2 ∧ (c.val 1).val = 1 ∧ (c.val 2).val = 1) ∨
    ((c.val 0).val = 1 ∧ (c.val 1).val = 2 ∧ (c.val 2).val = 1) ∨
    ((c.val 0).val = 1 ∧ (c.val 1).val = 1 ∧ (c.val 2).val = 2) := by
  by_cases h : ∃ i : Fin 3, (c.val i).val = 0
  · exact Or.inl h
  · have h0 : (c.val 0).val ≠ 0 := fun hz => h ⟨0, hz⟩
    have h1 : (c.val 1).val ≠ 0 := fun hz => h ⟨1, hz⟩
    have h2 : (c.val 2).val ≠ 0 := fun hz => h ⟨2, hz⟩
    have htotal := c.property.1
    omega

/-- The three interior placements become the canonical 112 shape after a
coordinate equivalence, preserving the physical child rather than replacing it. -/
theorem mme_square_child_positive_canonical_112
    {p : Fin 3 → ℕ} (c : RecursiveThinSplit.Split 4 p)
    (hpos : ∀ i : Fin 3, 0 < (c.val i).val) :
    ∃ e : Equiv.Perm (Fin 3),
      (c.val (e 0)).val = 1 ∧ (c.val (e 1)).val = 1 ∧ (c.val (e 2)).val = 2 := by
  rcases mme_square_child_boundary_or_permuted_112 c with hz | h | h | h
  · obtain ⟨i, hi⟩ := hz
    exact (Nat.ne_of_gt (hpos i) hi).elim
  · refine ⟨Equiv.swap 0 2, ?_⟩
    simpa using And.intro h.2.2 (And.intro h.2.1 h.1)
  · refine ⟨Equiv.swap 1 2, ?_⟩
    simpa using And.intro h.1 (And.intro h.2.2 h.2.1)
  · exact ⟨Equiv.refl _, h⟩

/-- Every released interior child is covered by boundary extraction or a
coordinate permutation of the canonical 112 extraction. -/
theorem solution
    (s : Fin 45) (c : Cell 4 6 (parent s)) :
    (∃ i : Fin 3, (c.2.val i).val = 0) ∨
      ∃ e : Equiv.Perm (Fin 3),
        (c.2.val (e 0)).val = 1 ∧ (c.2.val (e 1)).val = 1 ∧
          (c.2.val (e 2)).val = 2 := by
  by_cases h : ∃ i : Fin 3, (c.2.val i).val = 0
  · exact Or.inl h
  · apply Or.inr
    apply mme_square_child_positive_canonical_112 c.2
    intro i
    exact Nat.pos_of_ne_zero (fun hz => h ⟨i, hz⟩)


#print axioms solution

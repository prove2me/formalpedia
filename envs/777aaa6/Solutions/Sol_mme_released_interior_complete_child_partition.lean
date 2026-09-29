-- Prove2me | solution 1 for mme_released_interior_complete_child_partition
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T06:09:36.295631+00:00
-- url     : https://prove2.me/submissions/a99f21e6-8c80-4630-b90b-098dbd66285f

import Theorems.Thm_mme_released_interior_child_boundary_or_canonical_112
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic.Choose
import Mathlib.Tactic.FinCases

open MME MME.RecursiveYZ MME.ReleasedInterior

/-- Every released recipe has a complete finite partition into boundary and
112 children, with the zero or doubled coordinate specified for every cell. -/
theorem solution (s : Fin 45) :
    ∃ (nB nI : ℕ) (e : (Fin nB ⊕ Fin nI) ≃ Cell 4 6 (parent s))
      (zB : Fin nB → Fin 3) (zI : Fin nI → Fin 3),
      (∀ j, ((e (.inl j)).2.val (zB j)).val = 0) ∧
      (∀ j i, ((e (.inr j)).2.val i).val = if i = zI j then 2 else 1) := by
  classical
  let boundary : Cell 4 6 (parent s) → Prop := fun c => ∃ i, (c.2.val i).val = 0
  let B := {c : Cell 4 6 (parent s) // boundary c}
  let I := {c : Cell 4 6 (parent s) // ¬ boundary c}
  let eb := (Fintype.equivFin B).symm
  let ei := (Fintype.equivFin I).symm
  let e := (Equiv.sumCongr eb ei).trans (Equiv.sumCompl boundary)
  have hb : ∀ j, ∃ z, ((e (.inl j)).2.val z).val = 0 := fun j => (eb j).property
  have hi : ∀ j, ∃ z, ∀ i, ((e (.inr j)).2.val i).val = if i = z then 2 else 1 := by
    intro j
    have hc := mme_released_interior_child_boundary_or_canonical_112 s (ei j).val
    rcases hc with hz | ⟨p, h0, h1, h2⟩
    · exact ((ei j).property hz).elim
    · refine ⟨p 2, ?_⟩
      intro i
      change ((ei j).val.2.val i).val = if i = p 2 then 2 else 1
      have hinv := p.apply_symm_apply i
      generalize p.symm i = v at hinv
      fin_cases v
      · have hne : i ≠ p 2 := by rw [← hinv]; exact p.injective.ne (by decide)
        rw [if_neg hne]
        simpa only [← hinv] using h0
      · have hne : i ≠ p 2 := by rw [← hinv]; exact p.injective.ne (by decide)
        rw [if_neg hne]
        simpa only [← hinv] using h1
      · have heq : i = p 2 := hinv.symm
        rw [if_pos heq, heq]
        exact h2
  choose zB hzB using hb
  choose zI hzI using hi
  exact ⟨Fintype.card B, Fintype.card I, e, zB, zI, hzB, hzI⟩


#print axioms solution

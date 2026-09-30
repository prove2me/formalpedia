-- Prove2me | solution 1 for lean_workbook_plus_64280
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:02:58.879866+00:00
-- url     : https://prove2.me/submissions/4e9867ba-b9f2-41af-9d96-dae8454c0e14

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) (a : Fin n → ℝ) (h : ∑ i, a i < n) : ∃ i, a i < 1   := by
  by_contra! hnot
  have hn : (n : ℝ) ≤ ∑ i, a i := by
    simpa using (Finset.sum_le_sum (s := Finset.univ)
      (f := fun _ : Fin n => (1 : ℝ)) (g := a) (fun i _ => hnot i))
  linarith

#print axioms solution

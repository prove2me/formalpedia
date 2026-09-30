-- Prove2me | solution 1 for lean_workbook_plus_11657
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T17:50:57.666054+00:00
-- url     : https://prove2.me/submissions/0adf2835-ee3f-441a-8700-de4c518c849d

import Mathlib
set_option autoImplicit false

theorem solution (c : ℝ) : -3 * (c + 1) * (c - 13/3) ≥ 0 ↔ -1 ≤ c ∧ c ≤ 13/3   := by
  constructor
  · intro h
    constructor
    · by_contra! hc
      have hp : 0 < (c + 1) * (c - 13 / 3) :=
        mul_pos_of_neg_of_neg (by linarith) (by linarith)
      nlinarith
    · by_contra! hc
      have hp : 0 < (c + 1) * (c - 13 / 3) :=
        mul_pos (by linarith) (by linarith)
      nlinarith
  · rintro ⟨hl, hu⟩
    have hp : (c + 1) * (c - 13 / 3) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)
    nlinarith

#print axioms solution

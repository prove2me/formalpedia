-- Prove2me | solution 1 for lean_workbook_plus_27297
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:59:34.555779+00:00
-- url     : https://prove2.me/submissions/49798da9-fec7-4d89-b9fd-a70e428d185b

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (x : ℝ) (hx : x ≠ -1) (h : x ≠ 3) :
    (x - 2) * (x + 1) ^ 2 / (x - 3) < 0 ↔ 2 < x ∧ x < 3 := by
  have hs : 0 < (x + 1) ^ 2 := sq_pos_of_ne_zero (by intro he; apply hx; linarith)
  constructor
  · intro hn
    rcases div_neg_iff.mp hn with hcase | hcase
    · constructor
      · by_contra he
        have hx2 : x - 2 ≤ 0 := by linarith
        have hp := mul_nonpos_of_nonpos_of_nonneg hx2 (le_of_lt hs)
        linarith [hcase.1]
      · linarith [hcase.2]
    · have hx2 : 0 ≤ x - 2 := by linarith [hcase.2]
      have hp := mul_nonneg hx2 (le_of_lt hs)
      linarith [hcase.1]
  · rintro ⟨hlo, hhi⟩
    exact div_neg_of_pos_of_neg (mul_pos (by linarith) hs) (by linarith)

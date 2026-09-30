-- Prove2me | solution 1 for lean_workbook_plus_81212
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:07:03.445521+00:00
-- url     : https://prove2.me/submissions/544ef12b-0528-4797-a2e1-ff2ef1cd891d

import Mathlib

theorem solution (x y : ℝ) (h : ∀ ε : ℝ, ε > 0 → x ≤ y + ε) : x ≤ y := by
  by_contra hxy
  have hpos : 0 < (x - y) / 2 := by linarith
  have hsmall := h ((x - y) / 2) hpos
  linarith

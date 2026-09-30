-- Prove2me | solution 1 for lean_workbook_plus_30714
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:15:45.081405+00:00
-- url     : https://prove2.me/submissions/639ad171-b260-4a51-9c7f-135c899cfad4

import Mathlib.Analysis.Complex.Basic

theorem solution (x : ℕ → ℝ) (hx : x 1 = 0 ∧ x 2 = -5 ∧ x 3 = -2) : x 1 = 0 ∧ x 2 = -5 ∧ x 3 = -2 := hx

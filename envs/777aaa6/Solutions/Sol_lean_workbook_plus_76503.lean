-- Prove2me | solution 1 for lean_workbook_plus_76503
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:27:50.787558+00:00
-- url     : https://prove2.me/submissions/7fb3efe3-ecd8-4da2-a238-6d8b985dfb20

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (i : ℕ) (x : ℕ → ℝ) (hx : ∀ i, 0 < x i) (h : ∀ i, 1 - x (i + 1) = (1 - Real.sqrt (x i))^2 / (1 + x i)) : 1 - x (i + 1) = (1 - Real.sqrt (x i))^2 / (1 + x i) := by
  (intros; simp_all)

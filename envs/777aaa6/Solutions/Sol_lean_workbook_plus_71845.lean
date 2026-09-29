-- Prove2me | solution 1 for lean_workbook_plus_71845
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:45.841807+00:00
-- url     : https://prove2.me/submissions/57e5bc8c-89f7-4bb6-95f6-91eddf599a73

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (k : ℤ) (U : Set (ℝ × ℝ)) (hU : U = {p : ℝ × ℝ | p ≠ (0, 0)}) :
  ∀ p : ℝ × ℝ, (p ∈ U ↔ p ≠ (0, 0)) := by
  (intros; simp_all)

-- Prove2me | solution 2 for lean_workbook_plus_16613
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:21:22.965574+00:00
-- url     : https://prove2.me/submissions/c3c1404e-a464-4ba2-95b5-e58d1e966e58

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a : ℝ) (ha : 0 < a) (z : ℂ) (hz : z ≠ 0) (h : ‖z + 1/z‖ = a) : ‖z‖ ∈ Set.Ioi 0 ∪ Set.Ioi a := by
  (intros; simp_all)

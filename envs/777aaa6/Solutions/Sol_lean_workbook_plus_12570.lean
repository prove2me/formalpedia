-- Prove2me | solution 1 for lean_workbook_plus_12570
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:45.938616+00:00
-- url     : https://prove2.me/submissions/6de4e541-794b-49bf-b09e-2ba1588e3ba2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (t : ℝ)
  (h₀ : 0 < t)
  (h₁ : t ≤ 1 / 2) :
  t ∈ Set.Ioc 0 (1 / 2) := by
  (intros; simp_all)

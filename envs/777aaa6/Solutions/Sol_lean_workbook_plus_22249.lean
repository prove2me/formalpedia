-- Prove2me | solution 1 for lean_workbook_plus_22249
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:45:00.842493+00:00
-- url     : https://prove2.me/submissions/cdc8ae37-1a35-496a-8aa6-36f9628b7545

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (h₀ : y ≥ 3)
  (h₁ : y + z = x + 2 * y + 1) :
  z = x + y + 1 := by
  (intros; linarith)

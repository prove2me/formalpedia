-- Prove2me | solution 1 for lean_workbook_plus_17792
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:46.310326+00:00
-- url     : https://prove2.me/submissions/93719341-909b-4fdc-a585-57f220ed708c

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y : ℝ)
  (h₀ : 0 ≤ x ∧ 0 ≤ y) :
  (x + y) / 2 ≥ Real.sqrt (x * y) ↔ x^2 + y^2 + 2 * (x * y) ≥ 4 * (x * y) := by
  rcases h₀ with ⟨hx,hy⟩
  have hs := Real.sq_sqrt (mul_nonneg hx hy)
  have hn := Real.sqrt_nonneg (x*y)
  constructor
  · intro h
    nlinarith [sq_nonneg (x-y)]
  · intro h
    nlinarith

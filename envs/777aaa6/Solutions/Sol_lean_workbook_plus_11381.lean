-- Prove2me | solution 1 for lean_workbook_plus_11381
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:39:14.838631+00:00
-- url     : https://prove2.me/submissions/c55fca6a-f6ed-4382-a352-33e465666220

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z k : ℝ)
    (h₀ : x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0)
    (h₁ : x + y ≠ 0)
    (h₂ : y + z ≠ 0)
    (h₃ : z + x ≠ 0)
    (h₄ : x * y + y * z + z * x = k) :
    (x^2 + y^2 + 2 * k) / (x + y) + (y^2 + z^2 + 2 * k) / (y + z) + (z^2 + x^2 + 2 * k) / (z + x) = 4 * (x + y + z) := by
  (intros; field_simp; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (k), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - k), sq_nonneg (y - z), sq_nonneg (y - k), sq_nonneg (z - k), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (x + k), sq_nonneg (y + z), sq_nonneg (y + k), sq_nonneg (z + k)])

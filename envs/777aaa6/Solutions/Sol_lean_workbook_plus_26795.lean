-- Prove2me | solution 1 for lean_workbook_plus_26795
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:25:16.543743+00:00
-- url     : https://prove2.me/submissions/bfd60ebb-fe2e-4ed1-a754-42e8bb4fb572

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (v₀ : ℝ) (μ : ℝ) (g : ℝ) : (5 * v₀ ^ 2) / (2 * μ * g) = (2 * v₀ ^ 2) / (μ * g) + (v₀ ^ 2) / (2 * μ * g) := by
  (intros; ring)

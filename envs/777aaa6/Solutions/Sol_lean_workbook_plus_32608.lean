-- Prove2me | solution 1 for lean_workbook_plus_32608
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:13:30.014927+00:00
-- url     : https://prove2.me/submissions/bbb5d323-e33f-469a-9995-e5f6bc84035f

import Mathlib.Analysis.Complex.Basic

theorem solution {a b c x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0) : (a^2 / x + b^2 / y + c^2 / z) ≥ (a + b + c)^2 / (x + y + z) := by
  have two : ∀ (a b x y : ℝ), 0 < x → 0 < y → (a + b)^2 / (x + y) ≤ a^2 / x + b^2 / y := by
    intro a b x y hx hy
    rw [div_add_div _ _ hx.ne' hy.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg (a * y - b * x), mul_pos hx hy]
  have h1 := two (a + b) c (x + y) z (by positivity) hz
  have h2 := two a b x y hx hy
  linarith

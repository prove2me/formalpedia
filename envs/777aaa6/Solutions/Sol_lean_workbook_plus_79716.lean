-- Prove2me | solution 1 for lean_workbook_plus_79716
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:24:49.754563+00:00
-- url     : https://prove2.me/submissions/18cc5566-a50c-42fa-8a4b-099cdc3eee82

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

theorem solution (x y : ℝ) (hx : x > 0) (hy : y > 0) (hxy : x + 2 * y = 8) :
    (x + 1 / y) * (y + 1 / x) ≥ 4 := by
  have ht : 0 < x * y := mul_pos hx hy
  have heq : (x + 1 / y) * (y + 1 / x) = (x * y + 1)^2 / (x * y) := by
    field_simp
    <;> ring
  rw [heq]
  apply (le_div_iff₀ ht).2
  nlinarith [sq_nonneg (x * y - 1)]

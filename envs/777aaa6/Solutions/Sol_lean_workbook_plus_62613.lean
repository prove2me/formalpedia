-- Prove2me | solution 1 for lean_workbook_plus_62613
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:18:46.452276+00:00
-- url     : https://prove2.me/submissions/6b7b47d3-b0b8-414a-aa1c-57acb8b0ed8a

import Mathlib.Analysis.Complex.Basic

/-- Schur's inequality of degree 4 (`t = 2`), valid for all real numbers via the identity
`2 · LHS = Σ ((x - y)(x + y - z))²`. -/
theorem solution (x y z : ℝ) :
    x ^ 2 * (x - y) * (x - z) + y ^ 2 * (y - z) * (y - x) + z ^ 2 * (z - x) * (z - y) ≥ 0 := by
  nlinarith [sq_nonneg ((x - y) * (x + y - z)), sq_nonneg ((y - z) * (y + z - x)),
    sq_nonneg ((z - x) * (z + x - y))]

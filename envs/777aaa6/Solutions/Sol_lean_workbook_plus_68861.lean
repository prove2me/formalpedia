-- Prove2me | solution 1 for lean_workbook_plus_68861
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:14:27.085632+00:00
-- url     : https://prove2.me/submissions/1acedec5-bb88-4fb9-a4a3-4255607a8e38

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

private theorem supporting_line (u : ℝ) (hu : -1 ≤ u) :
    0 ≤ (u + 1) * (2 * u - 1) ^ 2 :=
  mul_nonneg (by linarith) (sq_nonneg _)

theorem solution (x y z t : ℝ)
    (hx : x ≥ -1) (hy : y ≥ -1) (hz : z ≥ -1) (ht : t ≥ -1)
    (h : x + y + z + t = 2) : x ^ 3 + y ^ 3 + z ^ 3 + t ^ 3 ≥ 1 / 2 := by
  nlinarith [supporting_line x hx, supporting_line y hy,
    supporting_line z hz, supporting_line t ht]

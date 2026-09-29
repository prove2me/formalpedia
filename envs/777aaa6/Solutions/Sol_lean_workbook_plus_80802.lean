-- Prove2me | solution 1 for lean_workbook_plus_80802
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:01:38.339297+00:00
-- url     : https://prove2.me/submissions/b4a98b64-59b5-48b1-9e03-cd718edd9739

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (p q : ℝ) (hp : 0 < p) (hq : 0 < q) : p * q^2 ≤ (p^3 + 2 * q^3) / 3 := by
  (intros; nlinarith [sq_nonneg (p), sq_nonneg (q), sq_nonneg (p - q), sq_nonneg (p + q), mul_pos hp hq])

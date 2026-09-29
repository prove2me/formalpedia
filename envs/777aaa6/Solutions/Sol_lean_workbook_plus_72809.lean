-- Prove2me | solution 1 for lean_workbook_plus_72809
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:21:13.893871+00:00
-- url     : https://prove2.me/submissions/5dc050cd-10c4-4df7-ae93-3435b44fecd6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {x y z : ℝ} (hx : 0 < x ∧ 0 < y ∧ 0 < z) (hx1 : y + z > x) (hx2 : z + x > y) (hx3 : x + y > z) : x ^ 2 + y ^ 2 + z ^ 2 ≤ 2 * x * y + 2 * y * z + 2 * z * x := by
  (intros; nlinarith)

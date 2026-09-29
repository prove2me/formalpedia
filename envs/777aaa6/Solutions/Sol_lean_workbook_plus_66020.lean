-- Prove2me | solution 1 for lean_workbook_plus_66020
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T07:05:53.67037+00:00
-- url     : https://prove2.me/submissions/5f3add2a-87aa-43ee-8890-412f30b8e2bb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c x y z : ℝ} (ha : a + b = 1 + c + x) (hb : b + c = 1 + a + y) (hc : a + c = 1 + b + z) (hx : x ≥ 0) (hy : y ≥ 0) (hz : z ≥ 0) : 18 * (x * y + y * z + z * x) + 16 * x * y * z + 6 * (x ^ 2 + y ^ 2 + z ^ 2) + 7 * (x * y * (x + y) + z * y * (z + y) + x * z * (x + z)) + 2 * (x ^ 3 + y ^ 3 + z ^ 3) ≥ 0 := by
  (intros; positivity)

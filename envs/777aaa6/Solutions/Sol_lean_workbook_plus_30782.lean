-- Prove2me | solution 1 for lean_workbook_plus_30782
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:35.766211+00:00
-- url     : https://prove2.me/submissions/92317840-2c61-45b6-a07b-367e5c44864f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (hx : x + y + z = 4) (hx' : 0 ≤ x) (hy' : 0 ≤ y) (hz' : 0 ≤ z) : (x^2 + 2) * (y^2 + 2) * (z^2 + 2) ≥ 0 := by
  (intros; positivity)

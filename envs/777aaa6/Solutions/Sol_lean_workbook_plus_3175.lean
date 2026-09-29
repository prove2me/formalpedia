-- Prove2me | solution 1 for lean_workbook_plus_3175
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:14:58.806616+00:00
-- url     : https://prove2.me/submissions/e555cf79-edd7-427a-9abf-cfd4a3218cd1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) (n : ℕ) : (x^(2 * n + 2) - y^(2 * n + 2)) = (x^(2 * n) - y^(2 * n)) * x^2 + y^(2 * n) * (x^2 - y^2) := by
  (intros; ring)

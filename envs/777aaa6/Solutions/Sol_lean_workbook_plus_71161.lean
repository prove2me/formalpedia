-- Prove2me | solution 1 for lean_workbook_plus_71161
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:19:19.585879+00:00
-- url     : https://prove2.me/submissions/52298814-a519-4f13-95f9-8610acb4d84e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  ∀ x y z : ℝ,
    (1 / 2) * (x + y + z) * ((x - y) ^ 2 + (y - z) ^ 2 + (z - x) ^ 2) =
    x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z := by
  (intros; linarith)

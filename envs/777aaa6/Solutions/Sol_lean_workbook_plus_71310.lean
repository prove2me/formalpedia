-- Prove2me | solution 1 for lean_workbook_plus_71310
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T05:52:08.6082+00:00
-- url     : https://prove2.me/submissions/0dd74d9a-9921-4366-83fc-5aeed442979a

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 4 + y ^ 4 + z ^ 4 = (x ^ 2 + y ^ 2 + z ^ 2) ^ 2 - 2 * (x ^ 2 * y ^ 2 + y ^ 2 * z ^ 2 + z ^ 2 * x ^ 2) := by
  (intros; linarith)

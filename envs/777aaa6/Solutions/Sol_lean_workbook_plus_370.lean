-- Prove2me | solution 1 for lean_workbook_plus_370
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:01.54867+00:00
-- url     : https://prove2.me/submissions/d2ff6ad1-fa64-4014-92e9-2b9639d0c4a8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {x y z : ℝ} : x ^ 3 + y ^ 3 + z ^ 3 - 3 * x * y * z = (x + y + z) * (x ^ 2 + y ^ 2 + z ^ 2 - x * y - y * z - x * z) := by
  (intros; linarith)

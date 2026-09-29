-- Prove2me | solution 1 for lean_workbook_plus_53854
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T08:45:45.641114+00:00
-- url     : https://prove2.me/submissions/47a70301-2bbc-4cea-b1fd-223fdc6917a2

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) : x ^ 2 * (1 - x) + y ^ 2 * (1 - y) + z ^ 2 * (1 - z) ≥ 0 → x ^ 3 + y ^ 3 + z ^ 3 ≤ x ^ 2 + y ^ 2 + z ^ 2 := by
  (intros; linarith)

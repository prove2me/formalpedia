-- Prove2me | solution 1 for lean_workbook_plus_36672
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:51:45.581578+00:00
-- url     : https://prove2.me/submissions/b5c86b88-807c-45aa-9b0e-ce7b258a1e05

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x y z : ℝ) (h1 : x = a + b - c) (h2 : y = a - b + c) (h3 : z = -a + b + c) : x + y + z = a + b + c := by
  (intros; linarith)

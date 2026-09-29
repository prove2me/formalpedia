-- Prove2me | solution 1 for lean_workbook_plus_1464
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:33:16.000932+00:00
-- url     : https://prove2.me/submissions/dc09082c-42e5-4b4a-8d85-5541751268bd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z a b c : ℝ) (hx : x = 1 / (1 + a)) (hy : y = 1 / (1 + b)) (hz : z = 1 / (1 + c)) : x ^ 2 + y ^ 2 + z ^ 2 = 1 / (1 + a) ^ 2 + 1 / (1 + b) ^ 2 + 1 / (1 + c) ^ 2 := by
  (intros; simp_all)

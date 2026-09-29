-- Prove2me | solution 1 for lean_workbook_plus_79092
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:26:45.48254+00:00
-- url     : https://prove2.me/submissions/ef37cd29-99aa-486d-a5a6-f2dee8156ce0

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b x x' y y' : ℝ) (ha : 0 < a) (hb : 0 < b) (hp : a * x ^ 2 + b * y ^ 2 = a * x' ^ 2 + b * y' ^ 2) : a * (x - x') * (x + x') = b * (y' - y) * (y + y') := by
  (intros; linarith)

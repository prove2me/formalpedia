-- Prove2me | solution 1 for lean_workbook_plus_52622
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:04:14.427396+00:00
-- url     : https://prove2.me/submissions/3245a2ae-a3aa-42d6-b8a7-f2108c2bc5e8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} (hx: a > 0 ∧ b > 0 ∧ c > 0) (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) : 3 * (a + b + c) ^ 2 ≥ 4 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  (intros; nlinarith)

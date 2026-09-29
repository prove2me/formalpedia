-- Prove2me | solution 1 for lean_workbook_plus_46907
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T09:51:53.689095+00:00
-- url     : https://prove2.me/submissions/64bf1ce2-4b29-4dd5-b58e-e9e3612e8e80

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c : ℝ} (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0) (hab : a ≥ b) (hbc : b ≥ c) (hca : c ≥ a) : a ^ 3 + b ^ 3 + c ^ 3 ≥ b * (a - c) ^ 2 + c * (b - a) ^ 2 + a * (c - b) ^ 2 + 3 * a * b * c := by
  (intros; nlinarith)

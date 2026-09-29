-- Prove2me | solution 1 for lean_workbook_plus_86
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:34:28.098012+00:00
-- url     : https://prove2.me/submissions/ce89be9d-bcec-40a1-b781-33186f52f9bd

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0) (habc : a * b * c = 1) (h : (1 - a * b) / (1 + b) + (1 - b * c) / (1 + c) + (1 - c * a) / (1 + a) = 0) : a * b * c ≤ 1 := by
  (intros; simp_all)

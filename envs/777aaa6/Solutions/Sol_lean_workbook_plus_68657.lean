-- Prove2me | solution 1 for lean_workbook_plus_68657
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-04T22:53:01.750459+00:00
-- url     : https://prove2.me/submissions/44ac639d-bb3a-4c8c-bf37-8c0fb10976bd

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem solution    (A B : ℝ)
    (h₀ : abs (A - B) > abs (A + B))
    : A * B < 0 := by
  have hsq : (abs (A + B)) ^ 2 < (abs (A - B)) ^ 2 := by
    nlinarith [abs_nonneg (A + B)]
  rw [sq_abs, sq_abs] at hsq
  nlinarith

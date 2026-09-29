-- Prove2me | solution 1 for lean_workbook_plus_30760
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:54:40.81461+00:00
-- url     : https://prove2.me/submissions/3e5c8cc0-7ed4-4e88-a8eb-aac3616f8fb3

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : x ≠ y)
  (h₁ : 0 < abs (x - y))
  (h₂ : 0 < abs (2 * (x - y))) :
  abs (2 * (x - y)) = 2 * abs (x - y) := by
  norm_num

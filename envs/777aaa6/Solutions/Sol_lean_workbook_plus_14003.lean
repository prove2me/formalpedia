-- Prove2me | solution 1 for lean_workbook_plus_14003
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T09:12:38.009141+00:00
-- url     : https://prove2.me/submissions/278ff452-2625-41f3-aa67-59f835f22b09

import Mathlib.Analysis.Complex.Basic

theorem solution (a : ℝ) (ha : a > 2) (x y : ℝ) :  x^2 + a * x * y + y^2 = 1 ↔ (x + a * y / 2)^2 - (a^2 - 4) * (y / 2)^2 = 1 := by
  constructor <;> intro h <;> linear_combination h

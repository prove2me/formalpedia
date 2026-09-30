-- Prove2me | solution 1 for lean_workbook_plus_43471
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:40:06.680644+00:00
-- url     : https://prove2.me/submissions/f7f7ced9-3559-4c26-b58d-ede12221675a

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) : 1 / (1 + a) + 1 / (1 + b) + 1 / (1 + c) = 1 → a * b * c ≥ 8 := by
  intro h
  have h1 : (1 + a) ≠ 0 := by positivity
  have h2 : (1 + b) ≠ 0 := by positivity
  have h3 : (1 + c) ≠ 0 := by positivity
  field_simp at h
  nlinarith [h, habc, ha, hb, hc]

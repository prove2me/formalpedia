-- Prove2me | solution 1 for lean_workbook_plus_65018
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:00:28.283971+00:00
-- url     : https://prove2.me/submissions/24fd8d03-133d-4350-8740-f9b07661fa09

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b c : ℝ) (ha : a ≥ 0) (hb : b ≥ 0) (hc : c ≥ 0) :
    9*(a^3+3*b^3+5*c^3) ≥ (a^2+3*b^2+5*c^2)*(a+3*b+5*c) := by
  have hab := mul_nonneg (sq_nonneg (a-b)) (add_nonneg ha hb)
  have hbc := mul_nonneg (sq_nonneg (b-c)) (add_nonneg hb hc)
  have hca := mul_nonneg (sq_nonneg (c-a)) (add_nonneg hc ha)
  nlinarith only [hab, hbc, hca]

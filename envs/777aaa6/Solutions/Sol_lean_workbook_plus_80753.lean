-- Prove2me | solution 1 for lean_workbook_plus_80753
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:24:30.335794+00:00
-- url     : https://prove2.me/submissions/4070f100-a8d3-46bf-a840-d6d8691ebd94

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem solution (a b : ℝ) (h : a+b ≥ 2) : a^4+b^4 ≥ a^3+b^3 := by
  have hs : 0 ≤ a+b := by linarith
  have hs1 : 0 ≤ a+b-1 := by linarith
  have hs2 : 0 ≤ a+b-2 := by linarith
  have h1 := mul_nonneg (pow_nonneg hs 3) hs2
  have h2 := mul_nonneg (mul_nonneg hs hs1) (sq_nonneg (a-b))
  have h3 := sq_nonneg ((a-b)^2)
  nlinarith

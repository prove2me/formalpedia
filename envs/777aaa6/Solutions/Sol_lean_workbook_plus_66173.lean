-- Prove2me | solution 1 for lean_workbook_plus_66173
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T04:22:19.746504+00:00
-- url     : https://prove2.me/submissions/5bdc2f93-6ed6-49f2-873f-aed2969c572a

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

private theorem triangle_gap_product (a b c : ℝ) :
    0 ≤ (|b| + |c| - |b + c|) * (|a| + |a + b + c| - |b + c|) := by
  have h : |b + c| ≤ |a| + |a + b + c| := by
    calc
      |b + c| = |(a + b + c) - a| := by congr 1; ring
      _ ≤ |a + b + c| + |a| := abs_sub _ _
      _ = |a| + |a + b + c| := by ring
  exact mul_nonneg (sub_nonneg.mpr (abs_add_le b c)) (sub_nonneg.mpr h)

theorem solution (a b c : ℝ) :
    |a| + |b| + |c| + |a + b + c| ≥ |b + c| + |c + a| + |a + b| := by
  have h1 := triangle_gap_product a b c
  have h2 := triangle_gap_product b c a
  have h3 := triangle_gap_product c a b
  have hs2 : b + c + a = a + b + c := by ring
  have hs3 : c + a + b = a + b + c := by ring
  rw [hs2] at h2
  rw [hs3] at h3
  have hprod : (|b + c| + |c + a| + |a + b|) *
      (|a| + |b| + |c| + |a + b + c|) ≤
      (|a| + |b| + |c| + |a + b + c|) *
      (|a| + |b| + |c| + |a + b + c|) := by
    nlinarith only [h1, h2, h3, sq_abs a, sq_abs b, sq_abs c,
      sq_abs (a + b + c), sq_abs (b + c), sq_abs (c + a), sq_abs (a + b)]
  by_cases hz : |a| + |b| + |c| + |a + b + c| = 0
  · linarith [abs_add_le b c, abs_add_le c a, abs_add_le a b, abs_nonneg (a + b + c)]
  · have hn : 0 ≤ |a| + |b| + |c| + |a + b + c| := by positivity
    exact le_of_mul_le_mul_right hprod (lt_of_le_of_ne hn (Ne.symm hz))

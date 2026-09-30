-- Prove2me | solution 1 for lean_workbook_plus_79770
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:05:03.462695+00:00
-- url     : https://prove2.me/submissions/10a9e8b8-a070-4823-bed5-5b693adbeafa

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

private lemma three_mul_le_cubes (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hc : 0 ≤ c) : 3 * a * b * c ≤ a ^ 3 + b ^ 3 + c ^ 3 := by
  have h := mul_nonneg (add_nonneg (add_nonneg ha hb) hc)
    (add_nonneg (add_nonneg (sq_nonneg (a - b)) (sq_nonneg (b - c)))
      (sq_nonneg (c - a)))
  nlinarith

theorem solution (a b c : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c) (h₁ : a * b * c ≥ 1) :
    a ^ 3 + b ^ 3 + c ^ 3 ≥ a * b + b * c + c * a := by
  have hsum := three_mul_le_cubes a b c h₀.1.le h₀.2.1.le h₀.2.2.le
  have hab := three_mul_le_cubes a b 1 h₀.1.le h₀.2.1.le zero_le_one
  have hbc := three_mul_le_cubes b c 1 h₀.2.1.le h₀.2.2.le zero_le_one
  have hca := three_mul_le_cubes c a 1 h₀.2.2.le h₀.1.le zero_le_one
  nlinarith

#print axioms solution

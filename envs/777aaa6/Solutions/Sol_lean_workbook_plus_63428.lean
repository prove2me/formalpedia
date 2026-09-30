-- Prove2me | solution 1 for lean_workbook_plus_63428
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:54:34.76766+00:00
-- url     : https://prove2.me/submissions/d36b05f4-0a70-49fe-b5c6-fc75adcc0921

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Linarith

theorem euclidean_repr_unique (a m n r s : ℤ) (ha : 0 < a)
    (hr : 0 ≤ r) (hra : r < a) (hs : 0 ≤ s) (hsa : s < a)
    (h : m * a + r = n * a + s) : m = n ∧ r = s := by
  have hmn : m = n := by
    rcases lt_trichotomy m n with hlt | heq | hlt
    · have hgap : 0 ≤ n - m - 1 := by omega
      nlinarith [mul_nonneg (le_of_lt ha) hgap]
    · exact heq
    · have hgap : 0 ≤ m - n - 1 := by omega
      nlinarith [mul_nonneg (le_of_lt ha) hgap]
  constructor
  · exact hmn
  · rw [hmn] at h
    omega

theorem solution (a : ℤ) (f : ℤ → ℕ → ℤ)
    (h₀ : ∀ n r, f n r = n * a + r) (h₁ : 0 < a) :
    Function.Injective f := by
  intro m n h
  have he := congrFun h 0
  rw [h₀ m 0, h₀ n 0] at he
  exact (euclidean_repr_unique a m n 0 0 h₁ (le_refl 0) h₁
    (le_refl 0) h₁ he).1

#print axioms solution

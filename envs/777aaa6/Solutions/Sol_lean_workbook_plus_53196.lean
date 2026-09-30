-- Prove2me | solution 1 for lean_workbook_plus_53196
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:45:52.61352+00:00
-- url     : https://prove2.me/submissions/47458426-d467-4337-abd6-f587d83462fe

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

theorem cubic_constraint_distance_identity (a b c : ℝ)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c = 5) :
    2 * (4 - (a * b * c + a + b + c)) =
      (a - 1) ^ 2 + (b - 1) ^ 2 + (c - 1) ^ 2 := by
  nlinarith

theorem cubic_constraint_full_bound (a b c : ℝ)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c = 5) :
    a * b * c + a + b + c ≤ 4 := by
  nlinarith [cubic_constraint_distance_identity a b c h,
    sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]

theorem cubic_constraint_equality (a b c : ℝ)
    (h : a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c = 5) :
    a * b * c + a + b + c = 4 ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · intro he
    have hd := cubic_constraint_distance_identity a b c h
    have ha : (a - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have hb : (b - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have hc : (c - 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1)]
    have ha1 : a - 1 = 0 := by simpa using ha
    have hb1 : b - 1 = 0 := by simpa using hb
    have hc1 : c - 1 = 0 := by simpa using hc
    exact ⟨by linarith, by linarith, by linarith⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

theorem solution (a b c : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (habc : a * b * c = 1) (h : a ^ 2 + b ^ 2 + c ^ 2 + 2 * a * b * c = 5) :
    a * b * c + a + b + c ≤ 4 :=
  cubic_constraint_full_bound a b c h

#print axioms solution
#print axioms cubic_constraint_full_bound
#print axioms cubic_constraint_equality

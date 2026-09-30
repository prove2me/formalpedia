-- Prove2me | solution 1 for lean_workbook_plus_71047
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:35:03.989395+00:00
-- url     : https://prove2.me/submissions/ace9d985-20f9-4508-9f83-7d1ac952b8a7

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

theorem fourth_power_gap (a b : ℝ) (hab : a * (a + b) ^ 2 = 4) :
    8 * (2 - a ^ 3 * b * (a ^ 2 + b ^ 2)) = a ^ 2 * (a - b) ^ 4 := by
  have hs : (a * (a + b) ^ 2) ^ 2 = 16 := by rw [hab]; norm_num
  linear_combination -hs

theorem unrestricted_bound (a b : ℝ) (hab : a * (a + b) ^ 2 = 4) :
    a ^ 3 * b * (a ^ 2 + b ^ 2) ≤ 2 := by
  have hg := fourth_power_gap a b hab
  have hn : 0 ≤ a ^ 2 * (a - b) ^ 4 := by positivity
  linarith

theorem equality_criterion (a b : ℝ) (hab : a * (a + b) ^ 2 = 4) :
    a ^ 3 * b * (a ^ 2 + b ^ 2) = 2 ↔ a = b := by
  have hg := fourth_power_gap a b hab
  constructor
  · intro h
    have ha : a ≠ 0 := by intro ha; subst a; norm_num at hab
    have hz : a ^ 2 * (a - b) ^ 4 = 0 := by linarith
    have hz' : (a - b) ^ 4 = 0 := (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ ha)
    exact sub_eq_zero.mp (pow_eq_zero hz')
  · intro h
    have hz : (a - b) ^ 4 = 0 := by rw [h]; norm_num
    rw [hz, mul_zero] at hg
    linarith

theorem solution (a b : ℝ) (_ha : 0 < a) (_hb : 0 < b)
    (hab : a * (a + b) ^ 2 = 4) : a ^ 3 * b * (a ^ 2 + b ^ 2) ≤ 2 :=
  unrestricted_bound a b hab

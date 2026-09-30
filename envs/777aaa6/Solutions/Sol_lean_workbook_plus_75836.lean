-- Prove2me | solution 1 for lean_workbook_plus_75836
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:33:37.914009+00:00
-- url     : https://prove2.me/submissions/1cf3f3e4-57e6-422f-a759-1fd3707ed28e

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

private theorem positive_pair_impossible (a b c : ℝ)
    (h : a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b) = 0)
    (hq : 0 < a * b + b * c + c * a) (hbc : 0 < b + c) : False := by
  have hab : 0 < a + b := by
    have hp : 0 < (a + b) * (b + c) := by nlinarith [sq_nonneg b]
    exact (mul_pos_iff_of_pos_right hbc).mp hp
  have hac : 0 < a + c := by
    have hp : 0 < (a + c) * (b + c) := by nlinarith [sq_nonneg c]
    exact (mul_pos_iff_of_pos_right hbc).mp hp
  have ht1 := mul_nonneg (sq_nonneg a) hbc.le
  have ht2 := mul_nonneg (sq_nonneg b) hac.le
  have ht3 := mul_nonneg (sq_nonneg c) hab.le
  have ha : a = 0 := by
    by_contra ha
    have hp := mul_pos (sq_pos_of_ne_zero ha) hbc
    linarith
  have hb : b = 0 := by
    by_contra hb
    have hp := mul_pos (sq_pos_of_ne_zero hb) hac
    linarith
  subst a
  subst b
  simpa using hq

theorem solution (a b c : ℝ)
    (h : a ^ 2 * (b + c) + b ^ 2 * (a + c) + c ^ 2 * (a + b) = 0) :
    a * b + b * c + c * a ≤ 0 := by
  by_contra hn
  have hq : 0 < a * b + b * c + c * a := lt_of_not_ge hn
  rcases lt_trichotomy (b + c) 0 with hbc | hbc | hbc
  · apply positive_pair_impossible (-a) (-b) (-c)
    · nlinarith [h]
    · nlinarith [hq]
    · linarith
  · have hc : c = -b := by linarith
    rw [hc] at hq
    nlinarith [sq_nonneg b]
  · exact positive_pair_impossible a b c h hq hbc

#print axioms solution

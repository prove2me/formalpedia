-- Prove2me | solution 1 for lean_workbook_plus_66879
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T06:45:02.699317+00:00
-- url     : https://prove2.me/submissions/1fbba6b0-0eac-45c8-873a-1737bcd016e9

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

theorem rational_lt_variable (x : ℝ) (hx : 0 < x) :
    (1 - x) / (1 + 3 * x) < x ↔ 1 / 3 < x := by
  rw [div_lt_iff₀ (show 0 < 1 + 3 * x by linarith)]
  constructor
  · intro h
    by_contra hn
    have hp := mul_nonneg (show 0 ≤ 1 - 3 * x by linarith)
      (show 0 ≤ x + 1 by linarith)
    nlinarith
  · intro h
    have hp := mul_pos (show 0 < 3 * x - 1 by linarith)
      (show 0 < x + 1 by linarith)
    nlinarith

theorem quadratic_lt_variable (x : ℝ) (hx : 0 < x) :
    3 * x ^ 2 - x - 1 < x ↔ x < 1 := by
  constructor
  · intro h
    by_contra hn
    have hp := mul_nonneg (show 0 ≤ x - 1 by linarith)
      (show 0 ≤ 3 * x + 1 by linarith)
    nlinarith
  · intro h
    have hp := mul_pos (show 0 < 1 - x by linarith)
      (show 0 < 3 * x + 1 by linarith)
    nlinarith

theorem formal_max_validity (x : ℝ) (hx : 0 < x) :
    max ((1 - x) / (1 + 3 * x)) (3 * x ^ 2 - x - 1) / (3 * x) < 1 / 3 ↔
      1 / 3 < x ∧ x < 1 := by
  rw [div_lt_iff₀ (show 0 < 3 * x by linarith)]
  have he : (1 : ℝ) / 3 * (3 * x) = x := by ring
  rw [he, max_lt_iff, rational_lt_variable x hx, quadratic_lt_variable x hx]

theorem source_max_validity (x : ℝ) (hx : 0 < x) :
    max ((1 - x) / (1 + 3 * x)) ((3 * x ^ 2 - x - 1) / (3 * x)) < 1 / 3 ↔
      1 / 3 < x ∧ x < 1 := by
  rw [max_lt_iff, div_lt_iff₀ (show 0 < 1 + 3 * x by linarith),
    div_lt_iff₀ (show 0 < 3 * x by linarith)]
  have he : (1 : ℝ) / 3 * (3 * x) = x := by ring
  rw [he, quadratic_lt_variable x hx]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

theorem solution (x : ℝ) (hx1 : 2 / 3 < x) (hx2 : x < 1) :
    max ((1 - x) / (1 + 3 * x)) (3 * x ^ 2 - x - 1) / (3 * x) < 1 / 3 :=
  (formal_max_validity x (by linarith)).2 ⟨by linarith, hx2⟩

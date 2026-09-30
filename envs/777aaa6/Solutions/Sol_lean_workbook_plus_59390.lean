-- Prove2me | solution 1 for lean_workbook_plus_59390
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:20:10.252318+00:00
-- url     : https://prove2.me/submissions/1008eb53-7968-4238-bb36-1e0eaf67176d

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ConstrainedCubicProduct

theorem parameters (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : 2 * a = a * b + b ^ 2) :
    a = (a + b) ^ 2 / (a + b + 2) ∧ b = 2 * (a + b) / (a + b + 2) := by
  have hd : a + b + 2 ≠ 0 := by positivity
  constructor <;> apply (eq_div_iff hd).mpr <;> nlinarith

theorem certificate (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : 2 * a = a * b + b ^ 2) :
    (a + b + 2) * ((a - b) * ((a + b) ^ 3 + 2 * a * b * (a + b) - 2 * a - 10 * b)) =
      (a - b) ^ 2 * ((a + b) ^ 3 + 10 * (a + b) ^ 2 + 22 * (a + b) + 20) := by
  let s := a + b
  have hap : a = s ^ 2 / (s + 2) := (parameters a b ha hb h).1
  have hbp : b = 2 * s / (s + 2) := (parameters a b ha hb h).2
  have hd : s + 2 ≠ 0 := by dsimp [s]; positivity
  change (s + 2) * ((a - b) * (s ^ 3 + 2 * a * b * s - 2 * a - 10 * b)) =
    (a - b) ^ 2 * (s ^ 3 + 10 * s ^ 2 + 22 * s + 20)
  rw [hap, hbp]
  field_simp
  ring

theorem bound (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : 2 * a = a * b + b ^ 2) :
    0 ≤ (a - b) * ((a + b) ^ 3 + 2 * a * b * (a + b) - 2 * a - 10 * b) := by
  have hd : 0 < a + b + 2 := by positivity
  have hp : 0 ≤ (a + b + 2) *
      ((a - b) * ((a + b) ^ 3 + 2 * a * b * (a + b) - 2 * a - 10 * b)) := by
    rw [certificate a b ha hb h]
    positivity
  exact (mul_nonneg_iff_of_pos_left hd).mp hp

theorem equality (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (h : 2 * a = a * b + b ^ 2) :
    (a - b) * ((a + b) ^ 3 + 2 * a * b * (a + b) - 2 * a - 10 * b) = 0 ↔
      a = 1 ∧ b = 1 := by
  constructor
  · intro he
    have hg := certificate a b ha hb h
    rw [he, mul_zero] at hg
    have hp : 0 < (a + b) ^ 3 + 10 * (a + b) ^ 2 + 22 * (a + b) + 20 := by positivity
    have hz := (mul_eq_zero.mp hg.symm).resolve_right (ne_of_gt hp)
    have hab : a = b := eq_of_sub_eq_zero (eq_zero_of_pow_eq_zero hz)
    have hf : a * (a - 1) = 0 := by rw [← hab] at h; nlinarith
    have ha1 : a = 1 := by
      have := (mul_eq_zero.mp hf).resolve_left (ne_of_gt ha)
      linarith
    exact ⟨ha1, hab ▸ ha1⟩
  · rintro ⟨rfl, rfl⟩
    ring

end ConstrainedCubicProduct

theorem solution (a b : ℝ) (hab : a > 0 ∧ b > 0) (h : 2 * a = a * b + b ^ 2) :
    (a - b) * ((a + b) ^ 3 + 2 * a * b * (a + b) - 2 * a - 10 * b) ≥ 0 :=
  ConstrainedCubicProduct.bound a b hab.1 hab.2 h

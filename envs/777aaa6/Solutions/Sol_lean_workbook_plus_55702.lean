-- Prove2me | solution 1 for lean_workbook_plus_55702
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:03:53.068021+00:00
-- url     : https://prove2.me/submissions/63d36e2c-f569-44b9-b885-dde5b9ad3f1b

import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

noncomputable def shiftedRatio (a b : ℝ) : ℝ :=
  (a ^ 2 + (b + 1) ^ 2) / (a ^ 2 + b ^ 2)

theorem lower_certificate {R : Type*} [CommRing R] (a b : R) :
    4 * (a ^ 2 + (b + 1) ^ 2) - (a ^ 2 + b ^ 2) =
      (a ^ 2 + b ^ 2 - 4) + 2 * (a ^ 2 + (b + 2) ^ 2) := by ring

theorem upper_certificate {R : Type*} [CommRing R] (a b : R) :
    9 * (a ^ 2 + b ^ 2) - 4 * (a ^ 2 + (b + 1) ^ 2) =
      3 * (a ^ 2 + b ^ 2 - 4) + 2 * (a ^ 2 + (b - 2) ^ 2) := by ring

theorem ratio_bounds (a b : ℝ) (h : 4 ≤ a ^ 2 + b ^ 2) :
    1 / 4 ≤ shiftedRatio a b ∧ shiftedRatio a b ≤ 9 / 4 := by
  have hp : 0 < a ^ 2 + b ^ 2 := by linarith
  unfold shiftedRatio
  constructor
  · apply (le_div_iff₀ hp).mpr
    nlinarith [lower_certificate a b, sq_nonneg a, sq_nonneg (b + 2)]
  · apply (div_le_iff₀ hp).mpr
    nlinarith [upper_certificate a b, sq_nonneg a, sq_nonneg (b - 2)]

theorem lower_equality (a b : ℝ) (h : 4 ≤ a ^ 2 + b ^ 2) :
    shiftedRatio a b = 1 / 4 ↔ a = 0 ∧ b = -2 := by
  constructor
  · intro he
    have hp : a ^ 2 + b ^ 2 ≠ 0 := by linarith
    have he' := (div_eq_iff hp).mp he
    have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg (b + 2)]
    have hb : (b + 2) ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg (b + 2)]
    exact ⟨sq_eq_zero_iff.mp ha, by have hh := sq_eq_zero_iff.mp hb; linarith⟩
  · rintro ⟨rfl, rfl⟩
    unfold shiftedRatio
    ring

theorem upper_equality (a b : ℝ) (h : 4 ≤ a ^ 2 + b ^ 2) :
    shiftedRatio a b = 9 / 4 ↔ a = 0 ∧ b = 2 := by
  constructor
  · intro he
    have hp : a ^ 2 + b ^ 2 ≠ 0 := by linarith
    have he' := (div_eq_iff hp).mp he
    have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg (b - 2)]
    have hb : (b - 2) ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg (b - 2)]
    exact ⟨sq_eq_zero_iff.mp ha, by have hh := sq_eq_zero_iff.mp hb; linarith⟩
  · rintro ⟨rfl, rfl⟩
    unfold shiftedRatio
    ring

theorem boundary_attainment (t : ℝ) (ht0 : 1 / 4 ≤ t) (ht1 : t ≤ 9 / 4) :
    ∃ a b : ℝ, a ^ 2 + b ^ 2 = 4 ∧ shiftedRatio a b = t := by
  let b := 2 * t - 5 / 2
  have hb0 : -2 ≤ b := by dsimp [b]; linarith
  have hb1 : b ≤ 2 := by dsimp [b]; linarith
  have hb : 0 ≤ 4 - b ^ 2 := by
    nlinarith [mul_nonneg (show 0 ≤ b + 2 by linarith) (show 0 ≤ 2 - b by linarith)]
  refine ⟨Real.sqrt (4 - b ^ 2), b, ?_, ?_⟩
  · rw [Real.sq_sqrt hb]
    ring
  · unfold shiftedRatio
    rw [Real.sq_sqrt hb]
    have hd : 4 - b ^ 2 + b ^ 2 = 4 := by ring
    rw [hd]
    dsimp [b]
    ring

theorem range_classification (t : ℝ) :
    (∃ a b : ℝ, 4 ≤ a ^ 2 + b ^ 2 ∧ shiftedRatio a b = t) ↔
      1 / 4 ≤ t ∧ t ≤ 9 / 4 := by
  constructor
  · rintro ⟨a, b, h, rfl⟩
    exact ratio_bounds a b h
  · rintro ⟨h0, h1⟩
    obtain ⟨a, b, hab, ht⟩ := boundary_attainment t h0 h1
    exact ⟨a, b, le_of_eq hab.symm, ht⟩

theorem solution (a b : ℝ) (h : a ^ 2 + b ^ 2 ≥ 4) :
    9 / 4 ≥ (a ^ 2 + (b + 1) ^ 2) / (a ^ 2 + b ^ 2) ∧
      (a ^ 2 + (b + 1) ^ 2) / (a ^ 2 + b ^ 2) ≥ 1 / 4 := by
  exact ⟨(ratio_bounds a b h).2, (ratio_bounds a b h).1⟩

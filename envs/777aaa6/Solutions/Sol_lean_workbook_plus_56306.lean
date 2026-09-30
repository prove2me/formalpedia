-- Prove2me | solution 1 for lean_workbook_plus_56306
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:43:54.17041+00:00
-- url     : https://prove2.me/submissions/04f64433-19ee-41f5-b6bf-edcbd5d3e895

import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

theorem cleared_identity {R : Type*} [CommRing R] (a b c : R) :
    (a + b) * (b + c) * (c + a) * (a + b + c) ^ 2 -
      24 * a * b * c * (a ^ 2 + b ^ 2 + c ^ 2) =
      c * ((a + b - 3 * c) * (a - b)) ^ 2 +
        a * ((b + c - 3 * a) * (b - c)) ^ 2 +
        b * ((c + a - 3 * b) * (c - a)) ^ 2 := by ring

theorem rational_identity {K : Type*} [Field K] (a b c : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hs : a + b + c ≠ 0) :
    (a + b) * (b + c) * (c + a) / a / b / c -
      24 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 =
      (a + b - 3 * c) ^ 2 * (a - b) ^ 2 / (a * b * (a + b + c) ^ 2) +
        (b + c - 3 * a) ^ 2 * (b - c) ^ 2 / (b * c * (a + b + c) ^ 2) +
        (c + a - 3 * b) ^ 2 * (c - a) ^ 2 / (c * a * (a + b + c) ^ 2) := by
  field_simp
  ring

noncomputable def ratioGap (a b c : ℝ) : ℝ :=
  (a + b) * (b + c) * (c + a) / a / b / c -
    24 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2

theorem positive_bound (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    0 ≤ ratioGap a b c := by
  unfold ratioGap
  rw [rational_identity a b c (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)
    (ne_of_gt (by positivity))]
  positivity

theorem weighted_squares_zero (u v w p q r : ℝ) (hu : 0 < u) (hv : 0 < v)
    (hw : 0 < w) (h : u * p ^ 2 + v * q ^ 2 + w * r ^ 2 = 0) :
    p = 0 ∧ q = 0 ∧ r = 0 := by
  have h1 : 0 ≤ u * p ^ 2 := by positivity
  have h2 : 0 ≤ v * q ^ 2 := by positivity
  have h3 : 0 ≤ w * r ^ 2 := by positivity
  have e1 : u * p ^ 2 = 0 := by linarith
  have e2 : v * q ^ 2 = 0 := by linarith
  have e3 : w * r ^ 2 = 0 := by linarith
  exact ⟨sq_eq_zero_iff.mp ((mul_eq_zero.mp e1).resolve_left (ne_of_gt hu)),
    sq_eq_zero_iff.mp ((mul_eq_zero.mp e2).resolve_left (ne_of_gt hv)),
    sq_eq_zero_iff.mp ((mul_eq_zero.mp e3).resolve_left (ne_of_gt hw))⟩

theorem factor_classification (a b c : ℝ)
    (h1 : (a + b - 3 * c) * (a - b) = 0)
    (h2 : (b + c - 3 * a) * (b - c) = 0)
    (h3 : (c + a - 3 * b) * (c - a) = 0) :
    (a = b ∧ b = c) ∨ (a = b ∧ c = 2 * a) ∨
      (b = c ∧ a = 2 * b) ∨ (c = a ∧ b = 2 * c) := by
  rcases mul_eq_zero.mp h1 with h1 | h1 <;>
    rcases mul_eq_zero.mp h2 with h2 | h2 <;>
    rcases mul_eq_zero.mp h3 with h3 | h3
  all_goals first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
    | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))

theorem positive_equality (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ratioGap a b c = 0 ↔
      (a = b ∧ b = c) ∨ (a = b ∧ c = 2 * a) ∨
        (b = c ∧ a = 2 * b) ∨ (c = a ∧ b = 2 * c) := by
  have hs : a + b + c ≠ 0 := ne_of_gt (by positivity)
  constructor
  · intro he
    unfold ratioGap at he
    field_simp [ne_of_gt ha, ne_of_gt hb, ne_of_gt hc, hs] at he
    have hz : c * ((a + b - 3 * c) * (a - b)) ^ 2 +
        a * ((b + c - 3 * a) * (b - c)) ^ 2 +
        b * ((c + a - 3 * b) * (c - a)) ^ 2 = 0 := by
      nlinarith [cleared_identity a b c]
    obtain ⟨h1, h2, h3⟩ := weighted_squares_zero _ _ _ _ _ _ hc ha hb hz
    exact factor_classification a b c h1 h2 h3
  · unfold ratioGap
    rw [rational_identity a b c (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc) hs]
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ring

theorem triangle_equality (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hab : c < a + b) (hbc : a < b + c) (hca : b < c + a) :
    ratioGap a b c = 0 ↔ a = b ∧ b = c := by
  rw [positive_equality a b c ha hb hc]
  constructor
  · rintro (h | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact h
    all_goals exfalso; linarith
  · exact Or.inl

theorem solution {a b c : ℝ} (ha : a > 0) (hb : b > 0) (hc : c > 0)
    (hab : a + b > c) (hbc : b + c > a) (hca : a + c > b) :
    (a + b) * (b + c) * (c + a) / a / b / c -
      24 * (a ^ 2 + b ^ 2 + c ^ 2) / (a + b + c) ^ 2 =
      (a + b - 3 * c) ^ 2 * (a - b) ^ 2 / (a * b * (a + b + c) ^ 2) +
        (b + c - 3 * a) ^ 2 * (b - c) ^ 2 / (b * c * (a + b + c) ^ 2) +
        (c + a - 3 * b) ^ 2 * (c - a) ^ 2 / (c * a * (a + b + c) ^ 2) :=
  rational_identity a b c (ne_of_gt ha) (ne_of_gt hb) (ne_of_gt hc)
    (ne_of_gt (by positivity))

-- Prove2me | solution 1 for lean_workbook_plus_20001
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:50:51.248697+00:00
-- url     : https://prove2.me/submissions/52db9ac0-4ba3-435c-84c1-e69930b0e06e

import Mathlib

namespace CubicConstraintThreeBounds

theorem product_gap (a b c : ℝ) :
    2 * (a ^ 3 + b ^ 3 + c ^ 3 - 3 * a * b * c) =
      (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) := by
  ring

theorem mixed_gap (a b c : ℝ) :
    108 * (a ^ 3 + b ^ 3 + c ^ 3 - a * b * c - 2 - 2 * (a + b * c - 2)) =
      4 * (a - 1) ^ 2 * (26 * a + 46) +
      (3 * (b + c) - 2 * (a + 2)) ^ 2 * (3 * (b + c) + (a + 2)) +
      27 * (3 * (b + c) + (a + 2)) * (b - c) ^ 2 := by
  ring

theorem cube_moment_gap (a b c : ℝ) :
    9 * (a ^ 3 + b ^ 3 + c ^ 3) - (a + b + c) ^ 3 =
      (a - b) ^ 2 * (4 * a + 4 * b + c) +
      (b - c) ^ 2 * (a + 4 * b + 4 * c) +
      (c - a) ^ 2 * (4 * a + b + 4 * c) := by
  ring

theorem product_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 3 + b ^ 3 + c ^ 3 = a * b * c + 2) : a * b * c ≤ 1 := by
  have hn : 0 ≤ (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) := by
    positivity
  linarith only [product_gap a b c, h, hn]

theorem mixed_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 3 + b ^ 3 + c ^ 3 = a * b * c + 2) : a + b * c ≤ 2 := by
  have h1 : 0 ≤ 4 * (a - 1) ^ 2 * (26 * a + 46) := by positivity
  have h2 : 0 ≤ (3 * (b + c) - 2 * (a + 2)) ^ 2 *
      (3 * (b + c) + (a + 2)) := by positivity
  have h3 : 0 ≤ 27 * (3 * (b + c) + (a + 2)) * (b - c) ^ 2 := by positivity
  linarith only [mixed_gap a b c, h, h1, h2, h3]

theorem sum_bound {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 3 + b ^ 3 + c ^ 3 = a * b * c + 2) : a + b + c ≤ 3 := by
  have hp := product_bound ha hb hc h
  have h1 : 0 ≤ (a - b) ^ 2 * (4 * a + 4 * b + c) := by positivity
  have h2 : 0 ≤ (b - c) ^ 2 * (a + 4 * b + 4 * c) := by positivity
  have h3 : 0 ≤ (c - a) ^ 2 * (4 * a + b + 4 * c) := by positivity
  have hcube : (a + b + c) ^ 3 ≤ (3 : ℝ) ^ 3 := by
    linarith only [cube_moment_gap a b c, h, hp, h1, h2, h3]
  exact (pow_le_pow_iff_left₀ (by positivity) (by norm_num) (by decide : 3 ≠ 0)).mp hcube

theorem product_equality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 3 + b ^ 3 + c ^ 3 = a * b * c + 2) :
    a * b * c = 1 ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · intro he
    have hz : (a + b + c) * ((a - b) ^ 2 + (b - c) ^ 2 + (c - a) ^ 2) = 0 := by
      linarith only [product_gap a b c, h, he]
    have hsq := (mul_eq_zero.mp hz).resolve_left (ne_of_gt (show 0 < a + b + c by positivity))
    have hab : a = b := by nlinarith only [hsq, sq_nonneg (b - c), sq_nonneg (c - a)]
    have hbc : b = c := by nlinarith only [hsq, sq_nonneg (a - b), sq_nonneg (c - a)]
    have ha3 : a ^ 3 = 1 := by simpa [← hab, ← hbc, pow_succ] using he
    have hf : (a - 1) * (a ^ 2 + a + 1) = 0 := by nlinarith only [ha3]
    have hf' := (mul_eq_zero.mp hf).resolve_right
      (ne_of_gt (show 0 < a ^ 2 + a + 1 by positivity))
    have ha1 : a = 1 := by linarith only [hf']
    exact ⟨ha1, hab ▸ ha1, hbc ▸ (hab ▸ ha1)⟩
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

theorem mixed_equality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 3 + b ^ 3 + c ^ 3 = a * b * c + 2) :
    a + b * c = 2 ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · intro he
    have h1 : 0 ≤ 4 * (a - 1) ^ 2 * (26 * a + 46) := by positivity
    have h2 : 0 ≤ (3 * (b + c) - 2 * (a + 2)) ^ 2 *
        (3 * (b + c) + (a + 2)) := by positivity
    have h3 : 0 ≤ 27 * (3 * (b + c) + (a + 2)) * (b - c) ^ 2 := by positivity
    have hz : 4 * (a - 1) ^ 2 * (26 * a + 46) = 0 := by
      linarith only [mixed_gap a b c, h, he, h1, h2, h3]
    have hz' := (mul_eq_zero.mp hz).resolve_right
      (ne_of_gt (show 0 < 26 * a + 46 by positivity))
    have ha1 : a = 1 := by nlinarith only [hz']
    apply (product_equality ha hb hc h).mp
    rw [ha1] at he ⊢
    nlinarith only [he]
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

theorem sum_equality {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 3 + b ^ 3 + c ^ 3 = a * b * c + 2) :
    a + b + c = 3 ↔ a = 1 ∧ b = 1 ∧ c = 1 := by
  constructor
  · intro he
    have h1 : 0 ≤ (a - b) ^ 2 * (4 * a + 4 * b + c) := by positivity
    have h2 : 0 ≤ (b - c) ^ 2 * (a + 4 * b + 4 * c) := by positivity
    have h3 : 0 ≤ (c - a) ^ 2 * (4 * a + b + 4 * c) := by positivity
    have hg := cube_moment_gap a b c
    rw [he] at hg
    have hp := product_bound ha hb hc h
    apply (product_equality ha hb hc h).mp
    linarith only [hg, h, hp, h1, h2, h3]
  · rintro ⟨rfl, rfl, rfl⟩
    norm_num

theorem source_bounds {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ^ 3 + b ^ 3 + c ^ 3 = a * b * c + 2) :
    a * b * c ≤ 1 ∧ a + b * c ≤ 2 ∧ a + b + c ≤ 3 :=
  ⟨product_bound ha hb hc h, mixed_bound ha hb hc h, sum_bound ha hb hc h⟩

theorem equality_model :
    (1 : ℝ) ^ 3 + 1 ^ 3 + 1 ^ 3 = 1 * 1 * 1 + 2 := by norm_num

theorem sharp_mixed_constant (k : ℝ) :
    (∀ a b c : ℝ, 0 < a → 0 < b → 0 < c →
      a ^ 3 + b ^ 3 + c ^ 3 = a * b * c + 2 → a + b * c ≤ k) ↔ 2 ≤ k := by
  constructor
  · intro h
    have hk := h 1 1 1 (by norm_num) (by norm_num) (by norm_num) equality_model
    norm_num at hk
    exact hk
  · intro hk a b c ha hb hc h
    exact (mixed_bound ha hb hc h).trans hk

end CubicConstraintThreeBounds

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (_habc : a * b * c = 1) (h : a ^ 3 + b ^ 3 + c ^ 3 = a * b * c + 2) :
    a * b * c ≤ 1 ∧ a + b * c ≤ 2 ∧ a + b + c ≤ 3 :=
  CubicConstraintThreeBounds.source_bounds ha hb hc h

#print axioms CubicConstraintThreeBounds.product_gap
#print axioms CubicConstraintThreeBounds.mixed_gap
#print axioms CubicConstraintThreeBounds.cube_moment_gap
#print axioms CubicConstraintThreeBounds.product_bound
#print axioms CubicConstraintThreeBounds.mixed_bound
#print axioms CubicConstraintThreeBounds.sum_bound
#print axioms CubicConstraintThreeBounds.product_equality
#print axioms CubicConstraintThreeBounds.mixed_equality
#print axioms CubicConstraintThreeBounds.sum_equality
#print axioms CubicConstraintThreeBounds.source_bounds
#print axioms CubicConstraintThreeBounds.equality_model
#print axioms CubicConstraintThreeBounds.sharp_mixed_constant
#print axioms solution

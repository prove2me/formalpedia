-- Prove2me | solution 1 for lean_workbook_plus_44014
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:01:48.601574+00:00
-- url     : https://prove2.me/submissions/4fcc4d17-cc72-41c9-8104-cd21a18e5190

import Mathlib

set_option autoImplicit false

open Polynomial

noncomputable section

namespace RealRootedCubicProductBound

def cubic (A B D : ℝ) : Polynomial ℝ :=
  C 1 * X ^ 3 + C A * X ^ 2 + C B * X + C D

theorem cubic_data (A B D : ℝ) :
    (cubic A B D).natDegree = 3 ∧ (cubic A B D).Monic := by
  constructor
  · exact natDegree_cubic (by norm_num : (1 : ℝ) ≠ 0)
  · exact leadingCoeff_cubic (by norm_num : (1 : ℝ) ≠ 0)

theorem splitting_iff (A B D : ℝ) :
    (cubic A B D).Splits ↔ exists x y z : ℝ,
      cubic A B D = (X - C x) * (X - C y) * (X - C z) := by
  constructor
  · intro hs
    have hc : (cubic A B D).roots.card = 3 := by
      rw [← hs.natDegree_eq_card_roots, (cubic_data A B D).1]
    obtain ⟨x, y, z, hr⟩ := Multiset.card_eq_three.mp hc
    refine ⟨x, y, z, ?_⟩
    simpa [hr, mul_assoc] using hs.eq_prod_roots_of_monic (cubic_data A B D).2
  · rintro ⟨x, y, z, h⟩
    rw [h]
    exact ((Splits.X_sub_C x).mul (Splits.X_sub_C y)).mul (Splits.X_sub_C z)

theorem factor_coefficients (A B D x y z : ℝ)
    (h : cubic A B D = (X - C x) * (X - C y) * (X - C z)) :
    A = -(x + y + z) ∧ B = x * y + x * z + y * z ∧ D = -x * y * z := by
  have h0 := congrArg (fun p : Polynomial ℝ => p.eval 0) h
  have h1 := congrArg (fun p : Polynomial ℝ => p.eval 1) h
  have hm := congrArg (fun p : Polynomial ℝ => p.eval (-1)) h
  simp [cubic] at h0 h1 hm
  constructor
  · nlinarith only [h0, h1, hm]
  constructor
  · nlinarith only [h0, h1, hm]
  · nlinarith only [h0]

theorem amgm_gap (u v w : ℝ) :
    2 * ((u + v + w) ^ 3 - 27 * u * v * w) =
      (u + v + w) * ((u - v) ^ 2 + (v - w) ^ 2 + (w - u) ^ 2) +
        6 * (u * (v - w) ^ 2 + v * (w - u) ^ 2 + w * (u - v) ^ 2) := by
  ring

theorem amgm_bound (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    27 * u * v * w ≤ (u + v + w) ^ 3 := by
  have h1 : 0 ≤ (u + v + w) * ((u - v) ^ 2 + (v - w) ^ 2 + (w - u) ^ 2) := by
    positivity
  have h2 : 0 ≤ u * (v - w) ^ 2 + v * (w - u) ^ 2 + w * (u - v) ^ 2 := by
    positivity
  linarith [amgm_gap u v w]

theorem amgm_equality (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    27 * u * v * w = (u + v + w) ^ 3 ↔ u = v ∧ v = w := by
  constructor
  · intro he
    by_cases hs : u + v + w = 0
    · constructor <;> linarith
    have hspos : 0 < u + v + w := by positivity
    have h2 : 0 ≤ u * (v - w) ^ 2 + v * (w - u) ^ 2 + w * (u - v) ^ 2 := by
      positivity
    have hq : (u - v) ^ 2 + (v - w) ^ 2 + (w - u) ^ 2 = 0 := by
      nlinarith [amgm_gap u v w, sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (w - u)]
    constructor <;> nlinarith [sq_nonneg (u - v), sq_nonneg (v - w), sq_nonneg (w - u)]
  · rintro ⟨rfl, rfl⟩
    ring

theorem root_square_sum (A B D x y z : ℝ)
    (h : cubic A B D = (X - C x) * (X - C y) * (X - C z)) :
    x ^ 2 + y ^ 2 + z ^ 2 = A ^ 2 - 2 * B := by
  obtain ⟨ha, hb, _⟩ := factor_coefficients A B D x y z h
  rw [ha, hb]
  ring

theorem coefficient_bound (A B D : ℝ) (hs : (cubic A B D).Splits) :
    27 * D ^ 2 ≤ (A ^ 2 - 2 * B) ^ 3 := by
  obtain ⟨x, y, z, hf⟩ := (splitting_iff A B D).mp hs
  have hm := root_square_sum A B D x y z hf
  have hd := (factor_coefficients A B D x y z hf).2.2
  have hg := amgm_bound (x ^ 2) (y ^ 2) (z ^ 2) (sq_nonneg x) (sq_nonneg y) (sq_nonneg z)
  rw [← hm, hd]
  nlinarith only [hg]

theorem root_equality (A B D x y z : ℝ)
    (hf : cubic A B D = (X - C x) * (X - C y) * (X - C z)) :
    27 * D ^ 2 = (A ^ 2 - 2 * B) ^ 3 ↔ x ^ 2 = y ^ 2 ∧ y ^ 2 = z ^ 2 := by
  have hm := root_square_sum A B D x y z hf
  have hd := (factor_coefficients A B D x y z hf).2.2
  rw [← hm, hd]
  have hp : 27 * (-x * y * z) ^ 2 = 27 * x ^ 2 * y ^ 2 * z ^ 2 := by ring
  rw [hp]
  exact amgm_equality (x ^ 2) (y ^ 2) (z ^ 2)
    (sq_nonneg x) (sq_nonneg y) (sq_nonneg z)

theorem coefficient_equality (A B D : ℝ) (hs : (cubic A B D).Splits) :
    27 * D ^ 2 = (A ^ 2 - 2 * B) ^ 3 ↔ exists r : ℝ,
      (A = -3 * r ∧ B = 3 * r ^ 2 ∧ D = -r ^ 3) ∨
      (A = -r ∧ B = -r ^ 2 ∧ D = r ^ 3) := by
  constructor
  · intro he
    obtain ⟨x, y, z, hf⟩ := (splitting_iff A B D).mp hs
    obtain ⟨hxy, hyz⟩ := (root_equality A B D x y z hf).mp he
    have hxz : z ^ 2 = x ^ 2 := hyz.symm.trans hxy.symm
    obtain ⟨hA, hB, hD⟩ := factor_coefficients A B D x y z hf
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxy.symm with hy | hy <;>
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hxz with hz | hz
    · refine ⟨x, Or.inl ?_⟩
      rw [hy, hz] at hA hB hD
      exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · refine ⟨x, Or.inr ?_⟩
      rw [hy, hz] at hA hB hD
      exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · refine ⟨x, Or.inr ?_⟩
      rw [hy, hz] at hA hB hD
      exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
    · refine ⟨-x, Or.inr ?_⟩
      rw [hy, hz] at hA hB hD
      exact ⟨by nlinarith, by nlinarith, by nlinarith⟩
  · rintro ⟨r, (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)⟩ <;> ring

def sourcePolynomial (a b : ℝ) : Polynomial ℝ :=
  cubic ((a - 1) * Real.sqrt 3) (-6 * a) b

theorem source_eval (a b x : ℝ) :
    (sourcePolynomial a b).eval x = x ^ 3 + (a - 1) * Real.sqrt 3 * x ^ 2 - 6 * a * x + b := by
  simp [sourcePolynomial, cubic]
  ring

theorem source_moment (a : ℝ) :
    ((a - 1) * Real.sqrt 3) ^ 2 - 2 * (-6 * a) = 3 * (a + 1) ^ 2 := by
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem source_bound (a b : ℝ) (hs : (sourcePolynomial a b).Splits) :
    |b| ≤ |a + 1| ^ 3 := by
  have h := coefficient_bound ((a - 1) * Real.sqrt 3) (-6 * a) b hs
  rw [source_moment] at h
  have hh : |b| ^ 2 ≤ (|a + 1| ^ 3) ^ 2 := by
    rw [sq_abs, ← pow_mul, Nat.mul_comm 3 2, pow_mul, sq_abs]
    nlinarith only [h]
  exact (sq_le_sq₀ (abs_nonneg b) (pow_nonneg (abs_nonneg (a + 1)) 3)).mp hh

theorem source_equality (a b : ℝ) (hs : (sourcePolynomial a b).Splits) :
    |b| = |a + 1| ^ 3 ↔ exists r : ℝ,
      ((a - 1) * Real.sqrt 3 = -3 * r ∧ -6 * a = 3 * r ^ 2 ∧ b = -r ^ 3) ∨
      ((a - 1) * Real.sqrt 3 = -r ∧ -6 * a = -r ^ 2 ∧ b = r ^ 3) := by
  have hc := coefficient_equality ((a - 1) * Real.sqrt 3) (-6 * a) b hs
  rw [source_moment] at hc
  rw [← hc]
  constructor
  · intro h
    have hsq := congrArg (fun t : ℝ => t ^ 2) h
    change |b| ^ 2 = (|a + 1| ^ 3) ^ 2 at hsq
    rw [sq_abs, ← pow_mul, Nat.mul_comm 3 2, pow_mul, sq_abs] at hsq
    nlinarith only [hsq]
  · intro h
    apply (sq_eq_sq₀ (abs_nonneg b) (pow_nonneg (abs_nonneg (a + 1)) 3)).mp
    rw [sq_abs, ← pow_mul, Nat.mul_comm 3 2, pow_mul, sq_abs]
    nlinarith only [h]

theorem equality_parameter_equations (a b : ℝ) (hs : (sourcePolynomial a b).Splits)
    (he : |b| = |a + 1| ^ 3) :
    a ^ 2 + 4 * a + 1 = 0 ∨ a ^ 2 - 4 * a + 1 = 0 := by
  obtain ⟨r, hr | hr⟩ := (source_equality a b hs).mp he
  · left
    have hsq := congrArg (fun t : ℝ => t ^ 2) hr.1
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hr.2.1]
  · right
    have hsq := congrArg (fun t : ℝ => t ^ 2) hr.1
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), hr.2.1]

theorem equality_parameter_roots (a b : ℝ) (hs : (sourcePolynomial a b).Splits)
    (he : |b| = |a + 1| ^ 3) :
    a = -2 + Real.sqrt 3 ∨ a = -2 - Real.sqrt 3 ∨
      a = 2 + Real.sqrt 3 ∨ a = 2 - Real.sqrt 3 := by
  have hr := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  rcases equality_parameter_equations a b hs he with ha | ha
  · have h : (a + 2) ^ 2 = (Real.sqrt 3) ^ 2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · left; linarith
    · right; left; linarith
  · have h : (a - 2) ^ 2 = (Real.sqrt 3) ^ 2 := by nlinarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · right; right; left; linarith
    · right; right; right; linarith

theorem sharp_model :
    (sourcePolynomial (2 - Real.sqrt 3) ((3 - Real.sqrt 3) ^ 3)).Splits ∧
      0 < |3 - Real.sqrt 3| ^ 3 ∧
      |(3 - Real.sqrt 3) ^ 3| = |(2 - Real.sqrt 3) + 1| ^ 3 := by
  have hr := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  have hp : 0 < 3 - Real.sqrt 3 := by nlinarith [Real.sqrt_nonneg (3 : ℝ)]
  have hA : ((2 - Real.sqrt 3) - 1) * Real.sqrt 3 = -(3 - Real.sqrt 3) := by nlinarith
  have hB : -6 * (2 - Real.sqrt 3) = -(3 - Real.sqrt 3) ^ 2 := by nlinarith
  refine ⟨?_, pow_pos (abs_pos.mpr (ne_of_gt hp)) 3, ?_⟩
  · apply (splitting_iff _ _ _).mpr
    refine ⟨3 - Real.sqrt 3, 3 - Real.sqrt 3, -(3 - Real.sqrt 3), ?_⟩
    change cubic _ _ _ = _
    rw [hA, hB]
    unfold cubic
    simp only [map_neg, map_pow, map_one]
    ring
  · rw [abs_pow]
    congr 2
    ring

theorem best_coefficient (k : ℝ) :
    (forall a b : ℝ, (sourcePolynomial a b).Splits → |b| ≤ k * |a + 1| ^ 3) ↔ 1 ≤ k := by
  constructor
  · intro h
    obtain ⟨hs, hp, he⟩ := sharp_model
    have hk := h (2 - Real.sqrt 3) ((3 - Real.sqrt 3) ^ 3) hs
    rw [he] at hk
    have heq : (2 - Real.sqrt 3 : ℝ) + 1 = 3 - Real.sqrt 3 := by ring
    rw [heq] at hk
    nlinarith
  · intro hk a b hs
    exact (source_bound a b hs).trans (by nlinarith [pow_nonneg (abs_nonneg (a + 1)) 3])

end RealRootedCubicProductBound

theorem solution (a b : ℝ) : exists x y z : ℝ,
    (x ^ 3 + (a - 1) * Real.sqrt 3 * x ^ 2 - 6 * a * x + b = 0 ∧
      y ^ 3 + (a - 1) * Real.sqrt 3 * y ^ 2 - 6 * a * y + b = 0 ∧
      z ^ 3 + (a - 1) * Real.sqrt 3 * z ^ 2 - 6 * a * z + b = 0) →
      |b| ≤ |a + 1| ^ 3 := by
  by_cases hb : b = 0
  · exact ⟨0, 0, 0, by simp [hb]⟩
  · refine ⟨0, 0, 0, ?_⟩
    intro h
    norm_num at h
    exact (hb h).elim

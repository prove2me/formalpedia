-- Prove2me | solution 1 for VectorSpaceOpt.minimum_variance_information_form
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T13:40:29.131762+00:00
-- url     : https://prove2.me/submissions/639875b4-82c5-4d8e-a190-2c56bc3ba572

import Mathlib
open Matrix


theorem solution {m n : ℕ}
    (W : Matrix (Fin m) (Fin n) ℝ)
    (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosDef)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : R.PosDef) :
    R * Wᵀ * (W * R * Wᵀ + Q)⁻¹ = (Wᵀ * Q⁻¹ * W + R⁻¹)⁻¹ * Wᵀ * Q⁻¹ ∧
    R - R * Wᵀ * (W * R * Wᵀ + Q)⁻¹ * W * R = (Wᵀ * Q⁻¹ * W + R⁻¹)⁻¹ := by
  classical
  have hQu : IsUnit Q.det := (Matrix.isUnit_iff_isUnit_det Q).1 hQ.isUnit
  have hRu : IsUnit R.det := (Matrix.isUnit_iff_isUnit_det R).1 hR.isUnit
  have hQi : (Q⁻¹).PosDef := Matrix.posDef_inv_iff.2 hQ
  have hRi : (R⁻¹).PosDef := Matrix.posDef_inv_iff.2 hR
  set T : Matrix (Fin m) (Fin m) ℝ := W * R * Wᵀ + Q with hTdef
  set S : Matrix (Fin n) (Fin n) ℝ := Wᵀ * Q⁻¹ * W + R⁻¹ with hSdef
  have hTpos : T.PosDef := by
    have h1 : (W * R * Wᵀ).PosSemidef := by
      have h := hR.posSemidef.mul_mul_conjTranspose_same W
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [hTdef]
    exact Matrix.PosDef.posSemidef_add h1 hQ
  have hSpos : S.PosDef := by
    have h2 : (Wᵀ * Q⁻¹ * W).PosSemidef := by
      have h := hQi.posSemidef.conjTranspose_mul_mul_same W
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
    rw [hSdef]
    exact Matrix.PosDef.posSemidef_add h2 hRi
  have hTu : IsUnit T.det := (Matrix.isUnit_iff_isUnit_det T).1 hTpos.isUnit
  have hSu : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hSpos.isUnit
  have hRR : R⁻¹ * R = 1 := Matrix.nonsing_inv_mul R hRu
  have hQQ : Q⁻¹ * Q = 1 := Matrix.nonsing_inv_mul Q hQu
  have hTT : T * T⁻¹ = 1 := Matrix.mul_nonsing_inv T hTu
  have hSS : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hSu
  have hL : S * (R * Wᵀ) = Wᵀ * Q⁻¹ * (W * R * Wᵀ) + Wᵀ := by
    rw [hSdef, Matrix.add_mul]
    congr 1
    · simp only [Matrix.mul_assoc]
    · rw [← Matrix.mul_assoc, hRR, Matrix.one_mul]
  have hRhs : Wᵀ * Q⁻¹ * T = Wᵀ * Q⁻¹ * (W * R * Wᵀ) + Wᵀ := by
    rw [hTdef, Matrix.mul_add]
    congr 1
    rw [Matrix.mul_assoc, hQQ, Matrix.mul_one]
  have step : S * (R * Wᵀ) = Wᵀ * Q⁻¹ * T := hL.trans hRhs.symm
  have key : S * (R * Wᵀ * T⁻¹) = Wᵀ * Q⁻¹ := by
    calc S * (R * Wᵀ * T⁻¹) = (S * (R * Wᵀ)) * T⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = (Wᵀ * Q⁻¹ * T) * T⁻¹ := by rw [step]
      _ = Wᵀ * Q⁻¹ := by rw [Matrix.mul_assoc, hTT, Matrix.mul_one]
  constructor
  · have h := congrArg (fun M : Matrix (Fin n) (Fin m) ℝ => S⁻¹ * M) key
    simp only at h
    rw [← Matrix.mul_assoc, hSS, Matrix.one_mul] at h
    rw [h, Matrix.mul_assoc]
  · have hSR : S * R = Wᵀ * Q⁻¹ * W * R + 1 := by
      rw [hSdef, Matrix.add_mul, hRR]
    have hSX : S * (R * Wᵀ * T⁻¹ * W * R) = Wᵀ * Q⁻¹ * W * R := by
      have e : R * Wᵀ * T⁻¹ * W * R = (R * Wᵀ * T⁻¹) * (W * R) := by
        simp only [Matrix.mul_assoc]
      rw [e, ← Matrix.mul_assoc, key]
      simp only [Matrix.mul_assoc]
    have h1 : S * (R - R * Wᵀ * T⁻¹ * W * R) = 1 := by
      rw [Matrix.mul_sub, hSR, hSX]
      abel
    have h2 := congrArg (fun M : Matrix (Fin n) (Fin n) ℝ => S⁻¹ * M) h1
    simp only at h2
    rw [← Matrix.mul_assoc, hSS, Matrix.one_mul, Matrix.mul_one] at h2
    exact h2

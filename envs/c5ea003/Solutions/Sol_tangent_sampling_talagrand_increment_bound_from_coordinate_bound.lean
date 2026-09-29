-- Prove2me | solution 1 for tangent_sampling_talagrand_increment_bound_from_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T03:39:46.900094+00:00
-- url     : https://prove2.me/submissions/9e463a64-e80d-4f2f-8eaa-c53e5d40f1ac

import Definitions.Def_matrix_completion_talagrand
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

open MatrixCompletion
open scoped Classical BigOperators

namespace MatrixCompletion

/-- Cauchy–Schwarz for the matrix Frobenius inner product. -/
theorem matrixInner_le_aux {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    |matrixInner X Y| ≤ frobeniusNorm X * frobeniusNorm Y := by
  have hfold : (∑ i : Fin n1, ∑ j : Fin n2, X i j * Y i j)
        = ∑ q : Fin n1 × Fin n2, X q.1 q.2 * Y q.1 q.2 :=
    (Fintype.sum_prod_type (fun q => X q.1 q.2 * Y q.1 q.2)).symm
  have hfoldX : (∑ i : Fin n1, ∑ j : Fin n2, X i j ^ 2)
        = ∑ q : Fin n1 × Fin n2, X q.1 q.2 ^ 2 :=
    (Fintype.sum_prod_type (fun q => X q.1 q.2 ^ 2)).symm
  have hfoldY : (∑ i : Fin n1, ∑ j : Fin n2, Y i j ^ 2)
        = ∑ q : Fin n1 × Fin n2, Y q.1 q.2 ^ 2 :=
    (Fintype.sum_prod_type (fun q => Y q.1 q.2 ^ 2)).symm
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
      (Finset.univ : Finset (Fin n1 × Fin n2))
      (fun q => X q.1 q.2) (fun q => Y q.1 q.2)
  unfold matrixInner frobeniusNorm frobeniusNormSq
  rw [hfold, hfoldX, hfoldY]
  set A := ∑ q : Fin n1 × Fin n2, X q.1 q.2 * Y q.1 q.2 with hA
  set SX := ∑ q : Fin n1 × Fin n2, X q.1 q.2 ^ 2 with hSX
  set SY := ∑ q : Fin n1 × Fin n2, Y q.1 q.2 ^ 2 with hSY
  have hSXnn : 0 ≤ SX := Finset.sum_nonneg (fun q _ => sq_nonneg _)
  have hrhs : Real.sqrt SX * Real.sqrt SY = Real.sqrt (SX * SY) :=
    (Real.sqrt_mul hSXnn SY).symm
  rw [hrhs, ← Real.sqrt_sq_eq_abs]
  apply Real.sqrt_le_sqrt
  exact hcs

end MatrixCompletion

theorem solution :
    ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
      (μ₀ : ℝ) (S : SVD M r),
      0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
      1 ≤ μ₀ →
      TangentCoordinateFrobeniusBound S
        (2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ)) →
      TangentSamplingTalagrandIncrementBound S
        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
        (2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ)) := by
  intro n₁ n₂ r m M μ₀ S hn1 hn2 hr hm hμ₀ hcoord
  intro X1 X2 hX1 hX2 i j
  set Pe := tangentProjection S (coordinateMatrix i j) with hPe
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hn1R : (0 : ℝ) < n₁ := by exact_mod_cast hn1
  have hn2R : (0 : ℝ) < n₂ := by exact_mod_cast hn2
  have hmaxN : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _)
  have hmaxR : (0 : ℝ) < (max n₁ n₂ : ℝ) := by exact_mod_cast hmaxN
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · subst hm0
    have hp0 : p = 0 := by rw [hp]; simp
    unfold tangentSamplingTalagrandCoefficient
    rw [← hPe, hp0]
    simp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hmpos
  have hPenn : 0 ≤ frobeniusNorm Pe := Real.sqrt_nonneg _
  have hPesq : frobeniusNorm Pe ^ 2 ≤ 2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ) := hcoord i j
  have hcs1 : |matrixInner X1 Pe| ≤ frobeniusNorm Pe := by
    calc |matrixInner X1 Pe| ≤ frobeniusNorm X1 * frobeniusNorm Pe := matrixInner_le_aux X1 Pe
      _ ≤ 1 * frobeniusNorm Pe := mul_le_mul_of_nonneg_right hX1 hPenn
      _ = frobeniusNorm Pe := by ring
  have hcs2 : |matrixInner Pe X2| ≤ frobeniusNorm Pe := by
    calc |matrixInner Pe X2| ≤ frobeniusNorm Pe * frobeniusNorm X2 := matrixInner_le_aux Pe X2
      _ ≤ frobeniusNorm Pe * 1 := mul_le_mul_of_nonneg_left hX2 hPenn
      _ = frobeniusNorm Pe := by ring
  have hppos : 0 < p := by rw [hp]; positivity
  have hpinvpos : 0 < p⁻¹ := inv_pos.mpr hppos
  have hppinn : 0 ≤ p⁻¹ * frobeniusNorm Pe := mul_nonneg hpinvpos.le hPenn
  unfold tangentSamplingTalagrandCoefficient
  rw [← hPe]
  rw [abs_mul, abs_mul, abs_of_pos hpinvpos]
  have hstep : p⁻¹ * |matrixInner X1 Pe| * |matrixInner Pe X2|
      ≤ p⁻¹ * frobeniusNorm Pe ^ 2 := by
    have h : p⁻¹ * |matrixInner X1 Pe| * |matrixInner Pe X2|
        ≤ p⁻¹ * frobeniusNorm Pe * frobeniusNorm Pe := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left hcs1 hpinvpos.le
      · exact hcs2
      · exact abs_nonneg _
      · exact hppinn
    calc p⁻¹ * |matrixInner X1 Pe| * |matrixInner Pe X2|
          ≤ p⁻¹ * frobeniusNorm Pe * frobeniusNorm Pe := h
      _ = p⁻¹ * frobeniusNorm Pe ^ 2 := by ring
  have hstep2 : p⁻¹ * frobeniusNorm Pe ^ 2
      ≤ p⁻¹ * (2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ)) :=
    mul_le_mul_of_nonneg_left hPesq hpinvpos.le
  have hpinv : p⁻¹ = ((n₁ : ℝ) * (n₂ : ℝ)) / (m : ℝ) := by rw [hp]; rw [inv_div]
  have hfinal : p⁻¹ * (2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ))
      ≤ 2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ) := by
    rw [hpinv]
    have hμ₀nn : 0 ≤ μ₀ := by linarith
    have hprod : (n₁ : ℝ) * (n₂ : ℝ) ≤ (max n₁ n₂ : ℝ) * (max n₁ n₂ : ℝ) := by
      have h1 : (n₁ : ℝ) ≤ (max n₁ n₂ : ℝ) := by exact_mod_cast le_max_left n₁ n₂
      have h2 : (n₂ : ℝ) ≤ (max n₁ n₂ : ℝ) := by exact_mod_cast le_max_right n₁ n₂
      calc (n₁ : ℝ) * (n₂ : ℝ) ≤ (max n₁ n₂ : ℝ) * (n₂ : ℝ) :=
            mul_le_mul_of_nonneg_right h1 hn2R.le
        _ ≤ (max n₁ n₂ : ℝ) * (max n₁ n₂ : ℝ) :=
            mul_le_mul_of_nonneg_left h2 hmaxR.le
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hmR]
    rw [mul_div_assoc', div_le_iff₀ hmaxR]
    have hc : (0 : ℝ) ≤ 2 * μ₀ * (r : ℝ) := by positivity
    have hcast : (↑(max n₁ n₂) : ℝ) = max (n₁ : ℝ) (n₂ : ℝ) := by push_cast; ring
    rw [hcast]
    calc (n₁ : ℝ) * (n₂ : ℝ) * (2 * μ₀ * (r : ℝ))
          ≤ (max (n₁:ℝ) (n₂:ℝ) * max (n₁:ℝ) (n₂:ℝ)) * (2 * μ₀ * (r : ℝ)) :=
            mul_le_mul_of_nonneg_right hprod hc
      _ = 2 * μ₀ * max (n₁:ℝ) (n₂:ℝ) * ↑r * max (n₁:ℝ) (n₂:ℝ) := by ring
  calc p⁻¹ * |matrixInner X1 Pe| * |matrixInner Pe X2|
        ≤ p⁻¹ * frobeniusNorm Pe ^ 2 := hstep
    _ ≤ p⁻¹ * (2 * μ₀ * (r : ℝ) / (max n₁ n₂ : ℝ)) := hstep2
    _ ≤ 2 * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) / (m : ℝ) := hfinal

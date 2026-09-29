-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_mean_prefactor_bound_from_coefficient_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-22T03:25:22.909997+00:00
-- url     : https://prove2.me/submissions/7f4cb2f8-ce9d-45d3-b219-9a8730ca134b

import Definitions.Def_matrix_completion_svd
import Definitions.Def_matrix_completion_tangent
import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped Classical BigOperators

open Matrix LinearMap MatrixCompletion

theorem solution :
    ∃ Cpref : ℝ, 0 < Cpref ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
        quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p =
          (p⁻¹ * (1 - p)) •
            ∑ w1 : Fin n₁ × Fin n₂,
              (signMatrix S w1.1 w1.2 *
                quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1) •
                coordinateMatrix w1.1 w1.2 →
        frobeniusNorm (signMatrix S) ≤ Real.sqrt (r : ℝ) →
        ∀ Ccoef : ℝ, 0 < Ccoef →
        let coeffScale : ℝ :=
          Ccoef * Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
            Real.rpow ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ)) ((3 : ℝ) / 2)
        QuadraticMiddleIndexDistinctMeanCoefficientBound Omega S p coeffScale →
        spectralNorm (quadraticNeumannMiddleIndexDistinctMeanContribution Omega S p) ≤
          (Cpref * Ccoef) * (p⁻¹ * (1 - p)) * Real.sqrt (r : ℝ) *
            Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
            Real.rpow ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ)) ((3 : ℝ) / 2) := by
  -- helper 1: spectralNorm (c . X) = |c| * spectralNorm X
  have spectralNorm_smul_aux : ∀ (c : ℝ) {a b : Nat} (X : RealMatrix a b),
      spectralNorm (c • X) = |c| * spectralNorm X := by
    intro c a b X
    unfold spectralNorm
    rw [show (Matrix.toEuclideanLin (c • X)) = c • (Matrix.toEuclideanLin X) from
      LinearMap.map_smul _ _ _]
    rw [map_smul, norm_smul]; simp [Real.norm_eq_abs]
  -- helper 2: spectralNorm X <= frobeniusNorm X
  have spectralNorm_le_frobeniusNorm_aux : ∀ {a b : Nat} (X : RealMatrix a b),
      spectralNorm X ≤ frobeniusNorm X := by
    intro a b X
    unfold spectralNorm
    have hfro_nonneg : 0 ≤ frobeniusNorm X := Real.sqrt_nonneg _
    refine ContinuousLinearMap.opNorm_le_bound _ hfro_nonneg ?_
    intro v
    rw [LinearMap.coe_toContinuousLinearMap']
    have hv_normsq : ‖v‖ ^ 2 = ∑ j : Fin b, (v j) ^ 2 := EuclideanSpace.real_norm_sq_eq v
    have hfv_normsq : ‖(Matrix.toEuclideanLin X) v‖ ^ 2 =
        ∑ i : Fin a, ((Matrix.toEuclideanLin X) v i) ^ 2 :=
      EuclideanSpace.real_norm_sq_eq _
    have hentry : ∀ i : Fin a, (Matrix.toEuclideanLin X) v i = ∑ j : Fin b, X i j * v j := by
      intro i; rfl
    rw [frobeniusNorm]
    have hnormv_nonneg : 0 ≤ ‖v‖ := norm_nonneg _
    have hfvnonneg : 0 ≤ ‖(Matrix.toEuclideanLin X) v‖ := norm_nonneg _
    have hrhs : Real.sqrt (frobeniusNormSq X) * ‖v‖
        = Real.sqrt (frobeniusNormSq X * (∑ j : Fin b, (v j) ^ 2)) := by
      rw [Real.sqrt_mul (by unfold frobeniusNormSq; positivity)]
      congr 1
      rw [← hv_normsq, Real.sqrt_sq hnormv_nonneg]
    rw [hrhs]
    rw [show ‖(Matrix.toEuclideanLin X) v‖ = Real.sqrt (‖(Matrix.toEuclideanLin X) v‖ ^ 2) from
      (Real.sqrt_sq hfvnonneg).symm]
    apply Real.sqrt_le_sqrt
    rw [hfv_normsq]
    calc ∑ i : Fin a, ((Matrix.toEuclideanLin X) v i) ^ 2
        = ∑ i : Fin a, (∑ j : Fin b, X i j * v j) ^ 2 := by
          apply Finset.sum_congr rfl; intro i _; rw [hentry i]
      _ ≤ ∑ i : Fin a, ((∑ j : Fin b, (X i j) ^ 2) * (∑ j : Fin b, (v j) ^ 2)) := by
          apply Finset.sum_le_sum; intro i _
          exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j => X i j) (fun j => v j)
      _ = (∑ i : Fin a, ∑ j : Fin b, (X i j) ^ 2) * (∑ j : Fin b, (v j) ^ 2) := by
          rw [← Finset.sum_mul]
      _ = frobeniusNormSq X * (∑ j : Fin b, (v j) ^ 2) := by rw [frobeniusNormSq]
  -- helper 3: coordinate-expansion entry
  have coordExpansion_entry_aux : ∀ {a b : Nat} (g : Fin a × Fin b → ℝ)
      (i : Fin a) (j : Fin b),
      (∑ w : Fin a × Fin b, g w • coordinateMatrix w.1 w.2) i j = g (i, j) := by
    intro a b g i j
    rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
    · simp [coordinateMatrix, Matrix.smul_apply]
    · intro w _ hw
      have hne : ¬ (i = w.1 ∧ j = w.2) := by
        rintro ⟨h1, h2⟩; exact hw (Prod.ext h1.symm h2.symm)
      simp only [Matrix.smul_apply, coordinateMatrix, hne, if_false, smul_zero]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- helper 4: frobenius bound for coordinate expansion
  have frob_coordExp_le_aux : ∀ {a b : Nat} (sgn : RealMatrix a b)
      (coeff : Fin a × Fin b → ℝ) (B : ℝ), 0 ≤ B → (∀ w, |coeff w| ≤ B) →
      frobeniusNorm (∑ w : Fin a × Fin b, (sgn w.1 w.2 * coeff w) • coordinateMatrix w.1 w.2)
        ≤ B * frobeniusNorm sgn := by
    intro a b sgn coeff B hB hcoeff
    unfold frobeniusNorm
    rw [← Real.sqrt_sq hB, ← Real.sqrt_mul (by positivity)]
    apply Real.sqrt_le_sqrt
    unfold frobeniusNormSq
    rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro i _
    rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro j _
    rw [coordExpansion_entry_aux (fun w => sgn w.1 w.2 * coeff w) i j]
    have he : (sgn i j * coeff (i, j)) ^ 2 = (sgn i j)^2 * (coeff (i,j))^2 := by ring
    rw [he]
    have hc2 : (coeff (i,j))^2 ≤ B^2 := by
      have := hcoeff (i,j); nlinarith [abs_nonneg (coeff (i,j)), sq_abs (coeff (i,j))]
    nlinarith [sq_nonneg (sgn i j), hc2]
  -- main proof
  refine ⟨1, one_pos, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn1 hn2 hr hm hμ0 hμ1 hA0 hA1
  intro p Omega heq hfrobsign Ccoef hCcoef coeffScale hcoeffbound
  have hnn : (0:ℝ) < (n₁:ℝ)*(n₂:ℝ) := by positivity
  have hp0 : 0 ≤ p := by simp only [p]; positivity
  have hp1 : p ≤ 1 := by simp only [p]; rw [div_le_one hnn]; exact_mod_cast hm
  have hq0 : 0 ≤ p⁻¹ * (1 - p) := mul_nonneg (by positivity) (by linarith)
  have hcs0 : 0 ≤ coeffScale := by
    simp only [coeffScale]
    apply mul_nonneg (mul_nonneg (le_of_lt hCcoef) (Real.sqrt_nonneg _))
    exact Real.rpow_nonneg (by positivity) _
  have hcb : ∀ w1, |quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1| ≤ coeffScale :=
    hcoeffbound
  rw [heq, spectralNorm_smul_aux, abs_of_nonneg hq0]
  have hM0 : spectralNorm (∑ w1 : Fin n₁ × Fin n₂,
        (signMatrix S w1.1 w1.2 * quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1) •
          coordinateMatrix w1.1 w1.2)
      ≤ coeffScale * Real.sqrt (r:ℝ) := by
    apply le_trans (spectralNorm_le_frobeniusNorm_aux _)
    apply le_trans (frob_coordExp_le_aux (signMatrix S)
      (fun w => quadraticMiddleIndexDistinctMeanCoefficient Omega S p w) coeffScale hcs0 hcb)
    exact mul_le_mul_of_nonneg_left hfrobsign hcs0
  calc (p⁻¹ * (1 - p)) * spectralNorm (∑ w1 : Fin n₁ × Fin n₂,
            (signMatrix S w1.1 w1.2 *
              quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1) •
              coordinateMatrix w1.1 w1.2)
        ≤ (p⁻¹ * (1 - p)) * (coeffScale * Real.sqrt (r:ℝ)) :=
          mul_le_mul_of_nonneg_left hM0 hq0
    _ = (1 * Ccoef) * (p⁻¹ * (1 - p)) * Real.sqrt (r : ℝ) *
          Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
          Real.rpow ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ)) ((3 : ℝ) / 2) := by
          simp only [coeffScale]; ring

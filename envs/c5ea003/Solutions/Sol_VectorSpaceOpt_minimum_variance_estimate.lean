-- Prove2me | solution 1 for VectorSpaceOpt.minimum_variance_estimate
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T13:59:25.202371+00:00
-- url     : https://prove2.me/submissions/1ee33d95-92cc-42c0-8336-40b5e9385758

import Mathlib
open Matrix MeasureTheory

section Moments
variable {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

/-- A product of two linear forms in `y` is a double sum of the entrywise products. -/
theorem vsm_quad_point (y : Ω → Fin m → ℝ)
    (A B : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) (ω : Ω) :
    A.mulVec (y ω) i * B.mulVec (y ω) j
      = ∑ k, ∑ l, (A i k * B j l) * (y ω k * y ω l) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem vsm_cross_point (y : Ω → Fin m → ℝ) (b : Ω → Fin n → ℝ)
    (K : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) (ω : Ω) :
    b ω i * K.mulVec (y ω) j = ∑ l, K j l * (b ω i * y ω l) := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem vsm_int_quad (y : Ω → Fin m → ℝ)
    (hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ)
    (A B : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) :
    Integrable (fun ω => A.mulVec (y ω) i * B.mulVec (y ω) j) μ := by
  refine Integrable.congr (f := fun ω => ∑ k, ∑ l, (A i k * B j l) * (y ω k * y ω l)) ?_ ?_
  · apply integrable_finset_sum
    intro k _
    apply integrable_finset_sum
    intro l _
    exact (hyy k l).const_mul _
  · exact Filter.Eventually.of_forall fun ω => (vsm_quad_point y A B i j ω).symm

theorem vsm_int_cross (y : Ω → Fin m → ℝ) (b : Ω → Fin n → ℝ)
    (hby : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => b ω i * y ω j) μ)
    (K : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) :
    Integrable (fun ω => b ω i * K.mulVec (y ω) j) μ := by
  refine Integrable.congr (f := fun ω => ∑ l, K j l * (b ω i * y ω l)) ?_ ?_
  · apply integrable_finset_sum
    intro l _
    exact (hby i l).const_mul _
  · exact Filter.Eventually.of_forall fun ω => (vsm_cross_point y b K i j ω).symm

theorem vsm_quad_int (y : Ω → Fin m → ℝ)
    (hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ)
    (Syy : Matrix (Fin m) (Fin m) ℝ) (hSyy : ∀ i j, ∫ ω, y ω i * y ω j ∂μ = Syy i j)
    (A B : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) :
    ∫ ω, A.mulVec (y ω) i * B.mulVec (y ω) j ∂μ = (A * Syy * Bᵀ) i j := by
  classical
  rw [integral_congr_ae (Filter.Eventually.of_forall (vsm_quad_point y A B i j))]
  rw [integral_finset_sum _ (fun k _ => by
    apply integrable_finset_sum; intro l _; exact (hyy k l).const_mul _)]
  have hk : ∀ k ∈ Finset.univ,
      (∫ ω, (∑ l, (A i k * B j l) * (y ω k * y ω l)) ∂μ)
        = ∑ l, (A i k * B j l) * Syy k l := by
    intro k _
    rw [integral_finset_sum _ (fun l _ => (hyy k l).const_mul _)]
    exact Finset.sum_congr rfl fun l _ => by rw [integral_const_mul, hSyy k l]
  rw [Finset.sum_congr rfl hk]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem vsm_cross_int (y : Ω → Fin m → ℝ) (b : Ω → Fin n → ℝ)
    (hby : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => b ω i * y ω j) μ)
    (Sby : Matrix (Fin n) (Fin m) ℝ) (hSby : ∀ i j, ∫ ω, b ω i * y ω j ∂μ = Sby i j)
    (K : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) :
    ∫ ω, b ω i * K.mulVec (y ω) j ∂μ = (Sby * Kᵀ) i j := by
  classical
  rw [integral_congr_ae (Filter.Eventually.of_forall (vsm_cross_point y b K i j))]
  rw [integral_finset_sum _ (fun l _ => (hby i l).const_mul _)]
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [integral_const_mul, hSby i l]; ring

/-- The error covariance of a linear estimate, in terms of second moments. -/
theorem vsm_err_cov (y : Ω → Fin m → ℝ) (b : Ω → Fin n → ℝ)
    (hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ)
    (hby : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => b ω i * y ω j) μ)
    (hbb : ∀ i j : Fin n, Integrable (fun ω => b ω i * b ω j) μ)
    (Syy : Matrix (Fin m) (Fin m) ℝ) (hSyy : ∀ i j, ∫ ω, y ω i * y ω j ∂μ = Syy i j)
    (Sby : Matrix (Fin n) (Fin m) ℝ) (hSby : ∀ i j, ∫ ω, b ω i * y ω j ∂μ = Sby i j)
    (Sbb : Matrix (Fin n) (Fin n) ℝ) (hSbb : ∀ i j, ∫ ω, b ω i * b ω j ∂μ = Sbb i j)
    (K : Matrix (Fin n) (Fin m) ℝ) (i j : Fin n) :
    ∫ ω, (b ω i - K.mulVec (y ω) i) * (b ω j - K.mulVec (y ω) j) ∂μ
      = Sbb i j - (Sby * Kᵀ) i j - (K * Sbyᵀ) i j + (K * Syy * Kᵀ) i j := by
  classical
  have hpoint : ∀ ω, (b ω i - K.mulVec (y ω) i) * (b ω j - K.mulVec (y ω) j)
      = b ω i * b ω j - b ω i * K.mulVec (y ω) j
        - b ω j * K.mulVec (y ω) i + K.mulVec (y ω) i * K.mulVec (y ω) j := by
    intro ω; ring
  have i1 : Integrable (fun ω => b ω i * b ω j) μ := hbb i j
  have i2 : Integrable (fun ω => b ω i * K.mulVec (y ω) j) μ := vsm_int_cross μ y b hby K i j
  have i3 : Integrable (fun ω => b ω j * K.mulVec (y ω) i) μ := vsm_int_cross μ y b hby K j i
  have i4 : Integrable (fun ω => K.mulVec (y ω) i * K.mulVec (y ω) j) μ :=
    vsm_int_quad μ y hyy K K i j
  have i12 : Integrable (fun ω => b ω i * b ω j - b ω i * K.mulVec (y ω) j) μ := i1.sub i2
  have i123 : Integrable (fun ω => b ω i * b ω j - b ω i * K.mulVec (y ω) j
      - b ω j * K.mulVec (y ω) i) μ := i12.sub i3
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2]
  rw [hSbb i j, vsm_cross_int μ y b hby Sby hSby K i j,
    vsm_cross_int μ y b hby Sby hSby K j i, vsm_quad_int μ y hyy Syy hSyy K K i j]
  have hsymm : (Sby * Kᵀ) j i = (K * Sbyᵀ) i j := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun l _ => mul_comm _ _
  rw [hsymm]

end Moments


theorem solution {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (y : Ω → Fin m → ℝ) (b : Ω → Fin n → ℝ)
    (hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ)
    (hby : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => b ω i * y ω j) μ)
    (hbb : ∀ i j : Fin n, Integrable (fun ω => b ω i * b ω j) μ)
    (Syy : Matrix (Fin m) (Fin m) ℝ) (hSyy : ∀ i j, ∫ ω, y ω i * y ω j ∂μ = Syy i j)
    (Sby : Matrix (Fin n) (Fin m) ℝ) (hSby : ∀ i j, ∫ ω, b ω i * y ω j ∂μ = Sby i j)
    (Sbb : Matrix (Fin n) (Fin n) ℝ) (hSbb : ∀ i j, ∫ ω, b ω i * b ω j ∂μ = Sbb i j)
    (hdet : IsUnit Syy.det)
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = Sby * Syy⁻¹)
    (K : Matrix (Fin n) (Fin m) ℝ) :
    (∀ i, ∫ ω, (K₀.mulVec (y ω) i - b ω i) ^ 2 ∂μ ≤
          ∫ ω, (K.mulVec (y ω) i - b ω i) ^ 2 ∂μ) ∧
    (∀ i j, ∫ ω, (b ω i - K₀.mulVec (y ω) i) * (b ω j - K₀.mulVec (y ω) j) ∂μ =
      (Sbb - Sby * Syy⁻¹ * Sbyᵀ) i j) := by
  classical
  have hSyysymm : Syyᵀ = Syy := by
    ext i j
    rw [Matrix.transpose_apply, ← hSyy j i, ← hSyy i j]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have hSyyinv : (Syy⁻¹)ᵀ = Syy⁻¹ := by rw [Matrix.transpose_nonsing_inv, hSyysymm]
  have hK₀Syy : K₀ * Syy = Sby := by
    rw [hK₀, Matrix.mul_assoc, Matrix.nonsing_inv_mul Syy hdet, Matrix.mul_one]
  have hSyyK₀T : Syy * K₀ᵀ = Sbyᵀ := by
    have h : (K₀ * Syy)ᵀ = Sbyᵀ := by rw [hK₀Syy]
    rw [Matrix.transpose_mul, hSyysymm] at h
    exact h
  have hdiag : ∀ (A : Matrix (Fin n) (Fin m) ℝ) (i : Fin n),
      (Sby * Aᵀ) i i = (A * Sbyᵀ) i i := by
    intro A i
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hquadnn : ∀ (D : Matrix (Fin n) (Fin m) ℝ) (i : Fin n), 0 ≤ (D * Syy * Dᵀ) i i := by
    intro D i
    rw [← vsm_quad_int μ y hyy Syy hSyy D D i i]
    exact integral_nonneg (fun ω => mul_self_nonneg _)
  have hsq : ∀ (A : Matrix (Fin n) (Fin m) ℝ) (i : Fin n),
      ∫ ω, (A.mulVec (y ω) i - b ω i) ^ 2 ∂μ
        = Sbb i i - (Sby * Aᵀ) i i - (A * Sbyᵀ) i i + (A * Syy * Aᵀ) i i := by
    intro A i
    have hfun : (fun ω => (A.mulVec (y ω) i - b ω i) ^ 2)
        = (fun ω => (b ω i - A.mulVec (y ω) i) * (b ω i - A.mulVec (y ω) i)) := by
      funext ω; ring
    rw [hfun]
    exact vsm_err_cov μ y b hyy hby hbb Syy hSyy Sby hSby Sbb hSbb A i i
  constructor
  · intro i
    rw [hsq K₀ i, hsq K i]
    obtain ⟨D, hD⟩ : ∃ D : Matrix (Fin n) (Fin m) ℝ, D = K - K₀ := ⟨_, rfl⟩
    have hKD : K = K₀ + D := by rw [hD]; abel
    have e1 : K * Syy * Kᵀ = K₀ * Syy * K₀ᵀ + Sby * Dᵀ + D * Sbyᵀ + D * Syy * Dᵀ := by
      rw [hKD, Matrix.transpose_add]
      simp only [Matrix.add_mul, Matrix.mul_add]
      rw [show K₀ * Syy * Dᵀ = Sby * Dᵀ by rw [hK₀Syy]]
      rw [show D * Syy * K₀ᵀ = D * Sbyᵀ by rw [Matrix.mul_assoc, hSyyK₀T]]
      abel
    have e2 : K * Sbyᵀ = K₀ * Sbyᵀ + D * Sbyᵀ := by rw [hKD, Matrix.add_mul]
    rw [hdiag K₀ i, hdiag K i, e1, e2]
    simp only [Matrix.add_apply]
    rw [hdiag D i]
    linarith [hquadnn D i]
  · intro i j
    rw [vsm_err_cov μ y b hyy hby hbb Syy hSyy Sby hSby Sbb hSbb K₀ i j]
    have h1 : Sby * K₀ᵀ = Sby * Syy⁻¹ * Sbyᵀ := by
      rw [hK₀, Matrix.transpose_mul, hSyyinv, ← Matrix.mul_assoc]
    have h2 : K₀ * Sbyᵀ = Sby * Syy⁻¹ * Sbyᵀ := by rw [hK₀]
    have h3 : K₀ * Syy * K₀ᵀ = Sby * Syy⁻¹ * Sbyᵀ := by
      rw [hK₀Syy, hK₀, Matrix.transpose_mul, hSyyinv, ← Matrix.mul_assoc]
    rw [h1, h2, h3]
    simp only [Matrix.sub_apply]
    ring

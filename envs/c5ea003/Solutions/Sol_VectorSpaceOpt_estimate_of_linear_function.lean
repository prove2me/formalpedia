-- Prove2me | solution 1 for VectorSpaceOpt.estimate_of_linear_function
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T14:03:11.16537+00:00
-- url     : https://prove2.me/submissions/1afad784-d090-4b42-a98b-7940591b9b70

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
section LinearMaps
variable {m n p : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

theorem vsm_lin_point (b : Ω → Fin n → ℝ) (y : Ω → Fin m → ℝ)
    (T : Matrix (Fin p) (Fin n) ℝ) (i : Fin p) (j : Fin m) (ω : Ω) :
    T.mulVec (b ω) i * y ω j = ∑ k, T i k * (b ω k * y ω j) := by
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem vsm_int_lin_cross (b : Ω → Fin n → ℝ) (y : Ω → Fin m → ℝ)
    (hby : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => b ω i * y ω j) μ)
    (T : Matrix (Fin p) (Fin n) ℝ) (i : Fin p) (j : Fin m) :
    Integrable (fun ω => T.mulVec (b ω) i * y ω j) μ := by
  refine Integrable.congr (f := fun ω => ∑ k, T i k * (b ω k * y ω j)) ?_ ?_
  · exact integrable_finset_sum _ fun k _ => (hby k j).const_mul _
  · exact Filter.Eventually.of_forall fun ω => (vsm_lin_point b y T i j ω).symm

theorem vsm_lin_cross_int (b : Ω → Fin n → ℝ) (y : Ω → Fin m → ℝ)
    (hby : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => b ω i * y ω j) μ)
    (Sby : Matrix (Fin n) (Fin m) ℝ) (hSby : ∀ i j, ∫ ω, b ω i * y ω j ∂μ = Sby i j)
    (T : Matrix (Fin p) (Fin n) ℝ) (i : Fin p) (j : Fin m) :
    ∫ ω, T.mulVec (b ω) i * y ω j ∂μ = (T * Sby) i j := by
  classical
  rw [integral_congr_ae (Filter.Eventually.of_forall (vsm_lin_point b y T i j))]
  rw [integral_finset_sum _ (fun k _ => (hby k j).const_mul _)]
  simp only [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => by rw [integral_const_mul, hSby k j]

end LinearMaps

section Optimality
variable {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- The minimum-variance estimate minimizes each component of the mean-square error. -/
theorem vsm_mv_optimal (y : Ω → Fin m → ℝ) (b : Ω → Fin n → ℝ)
    (hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ)
    (hby : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => b ω i * y ω j) μ)
    (hbb : ∀ i j : Fin n, Integrable (fun ω => b ω i * b ω j) μ)
    (Syy : Matrix (Fin m) (Fin m) ℝ) (hSyy : ∀ i j, ∫ ω, y ω i * y ω j ∂μ = Syy i j)
    (Sby : Matrix (Fin n) (Fin m) ℝ) (hSby : ∀ i j, ∫ ω, b ω i * y ω j ∂μ = Sby i j)
    (Sbb : Matrix (Fin n) (Fin n) ℝ) (hSbb : ∀ i j, ∫ ω, b ω i * b ω j ∂μ = Sbb i j)
    (hdet : IsUnit Syy.det)
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = Sby * Syy⁻¹)
    (K : Matrix (Fin n) (Fin m) ℝ) (i : Fin n) :
    ∫ ω, (K₀.mulVec (y ω) i - b ω i) ^ 2 ∂μ ≤
      ∫ ω, (K.mulVec (y ω) i - b ω i) ^ 2 ∂μ := by
  classical
  have hSyysymm : Syyᵀ = Syy := by
    ext a c
    rw [Matrix.transpose_apply, ← hSyy c a, ← hSyy a c]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  have hK₀Syy : K₀ * Syy = Sby := by
    rw [hK₀, Matrix.mul_assoc, Matrix.nonsing_inv_mul Syy hdet, Matrix.mul_one]
  have hSyyK₀T : Syy * K₀ᵀ = Sbyᵀ := by
    have h : (K₀ * Syy)ᵀ = Sbyᵀ := by rw [hK₀Syy]
    rw [Matrix.transpose_mul, hSyysymm] at h
    exact h
  have hdiag : ∀ (A : Matrix (Fin n) (Fin m) ℝ) (a : Fin n),
      (Sby * Aᵀ) a a = (A * Sbyᵀ) a a := by
    intro A a
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hquadnn : ∀ (D : Matrix (Fin n) (Fin m) ℝ) (a : Fin n), 0 ≤ (D * Syy * Dᵀ) a a := by
    intro D a
    rw [← vsm_quad_int μ y hyy Syy hSyy D D a a]
    exact integral_nonneg (fun ω => mul_self_nonneg _)
  have hsq : ∀ (A : Matrix (Fin n) (Fin m) ℝ) (a : Fin n),
      ∫ ω, (A.mulVec (y ω) a - b ω a) ^ 2 ∂μ
        = Sbb a a - (Sby * Aᵀ) a a - (A * Sbyᵀ) a a + (A * Syy * Aᵀ) a a := by
    intro A a
    have hfun : (fun ω => (A.mulVec (y ω) a - b ω a) ^ 2)
        = (fun ω => (b ω a - A.mulVec (y ω) a) * (b ω a - A.mulVec (y ω) a)) := by
      funext ω; ring
    rw [hfun]
    exact vsm_err_cov μ y b hyy hby hbb Syy hSyy Sby hSby Sbb hSbb A a a
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

end Optimality


theorem solution {m n p : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (y : Ω → Fin m → ℝ) (β : Ω → Fin n → ℝ)
    (hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ)
    (hβy : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => β ω i * y ω j) μ)
    (hββ : ∀ i j : Fin n, Integrable (fun ω => β ω i * β ω j) μ)
    (Syy : Matrix (Fin m) (Fin m) ℝ) (hSyy : ∀ i j, ∫ ω, y ω i * y ω j ∂μ = Syy i j)
    (Sβy : Matrix (Fin n) (Fin m) ℝ) (hSβy : ∀ i j, ∫ ω, β ω i * y ω j ∂μ = Sβy i j)
    (hdet : IsUnit Syy.det)
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = Sβy * Syy⁻¹)
    (T : Matrix (Fin p) (Fin n) ℝ) (Γ : Matrix (Fin p) (Fin m) ℝ) :
    ∀ i, ∫ ω, ((T * K₀).mulVec (y ω) i - T.mulVec (β ω) i) ^ 2 ∂μ ≤
         ∫ ω, (Γ.mulVec (y ω) i - T.mulVec (β ω) i) ^ 2 ∂μ := by
  classical
  intro i
  have hb'y : ∀ (a : Fin p) (j : Fin m),
      Integrable (fun ω => T.mulVec (β ω) a * y ω j) μ :=
    fun a j => vsm_int_lin_cross μ β y hβy T a j
  have hb'b' : ∀ a c : Fin p,
      Integrable (fun ω => T.mulVec (β ω) a * T.mulVec (β ω) c) μ :=
    fun a c => vsm_int_quad μ β hββ T T a c
  have hSb'y : ∀ (a : Fin p) (j : Fin m),
      ∫ ω, T.mulVec (β ω) a * y ω j ∂μ = (T * Sβy) a j :=
    fun a j => vsm_lin_cross_int μ β y hβy Sβy hSβy T a j
  have hTK₀ : T * K₀ = (T * Sβy) * Syy⁻¹ := by rw [hK₀, Matrix.mul_assoc]
  exact vsm_mv_optimal μ y (fun ω => T.mulVec (β ω)) hyy hb'y hb'b' Syy hSyy
    (T * Sβy) hSb'y (Matrix.of fun a c => ∫ ω, T.mulVec (β ω) a * T.mulVec (β ω) c ∂μ)
    (fun a c => rfl) hdet (T * K₀) hTK₀ Γ i

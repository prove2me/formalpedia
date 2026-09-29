-- Prove2me | solution 1 for VectorSpaceOpt.minimum_variance_W_form
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-26T14:06:00.08791+00:00
-- url     : https://prove2.me/submissions/b0c7340d-c6b9-422c-a8b8-404f86b36ccc

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


theorem solution {m n : ℕ} {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Matrix (Fin m) (Fin n) ℝ)
    (β : Ω → Fin n → ℝ) (ε : Ω → Fin m → ℝ) (y : Ω → Fin m → ℝ)
    (hy : ∀ ω i, y ω i = W.mulVec (β ω) i + ε ω i)
    (hββ : ∀ i j : Fin n, Integrable (fun ω => β ω i * β ω j) μ)
    (hεε : ∀ i j : Fin m, Integrable (fun ω => ε ω i * ε ω j) μ)
    (hεβ : ∀ (i : Fin m) (j : Fin n), Integrable (fun ω => ε ω i * β ω j) μ)
    (R : Matrix (Fin n) (Fin n) ℝ) (hR : ∀ i j, ∫ ω, β ω i * β ω j ∂μ = R i j)
    (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : ∀ i j, ∫ ω, ε ω i * ε ω j ∂μ = Q i j)
    (hcross : ∀ (i : Fin m) (j : Fin n), ∫ ω, ε ω i * β ω j ∂μ = 0)
    (hdet : IsUnit (W * R * Wᵀ + Q).det)
    (K₀ : Matrix (Fin n) (Fin m) ℝ) (hK₀ : K₀ = R * Wᵀ * (W * R * Wᵀ + Q)⁻¹)
    (K : Matrix (Fin n) (Fin m) ℝ) :
    (∀ i, ∫ ω, (K₀.mulVec (y ω) i - β ω i) ^ 2 ∂μ ≤
          ∫ ω, (K.mulVec (y ω) i - β ω i) ^ 2 ∂μ) ∧
    (∀ i j, ∫ ω, (β ω i - K₀.mulVec (y ω) i) * (β ω j - K₀.mulVec (y ω) j) ∂μ =
      (R - R * Wᵀ * (W * R * Wᵀ + Q)⁻¹ * W * R) i j) := by
  classical
  -- integrability of the mixed second moments
  have hβε : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => β ω i * ε ω j) μ := by
    intro i j
    have e : (fun ω => β ω i * ε ω j) = (fun ω => ε ω j * β ω i) := by funext ω; ring
    rw [e]; exact hεβ j i
  have hSβε : ∀ (i : Fin n) (j : Fin m), ∫ ω, β ω i * ε ω j ∂μ = (0 : Matrix (Fin n) (Fin m) ℝ) i j := by
    intro i j
    have e : (fun ω => β ω i * ε ω j) = (fun ω => ε ω j * β ω i) := by funext ω; ring
    rw [e, hcross j i]
    simp
  have hRsymm : Rᵀ = R := by
    ext i j
    rw [Matrix.transpose_apply, ← hR j i, ← hR i j]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
  -- second moments of `y`
  have hyy : ∀ i j : Fin m, Integrable (fun ω => y ω i * y ω j) μ := by
    intro i j
    have e : (fun ω => y ω i * y ω j)
        = (fun ω => W.mulVec (β ω) i * W.mulVec (β ω) j
            + W.mulVec (β ω) i * ε ω j + ε ω i * W.mulVec (β ω) j + ε ω i * ε ω j) := by
      funext ω; rw [hy ω i, hy ω j]; ring
    rw [e]
    have h2 : Integrable (fun ω => W.mulVec (β ω) i * ε ω j) μ :=
      vsm_int_lin_cross μ β ε hβε W i j
    have h3 : Integrable (fun ω => ε ω i * W.mulVec (β ω) j) μ := by
      have e3 : (fun ω => ε ω i * W.mulVec (β ω) j)
          = (fun ω => W.mulVec (β ω) j * ε ω i) := by funext ω; ring
      rw [e3]; exact vsm_int_lin_cross μ β ε hβε W j i
    exact (((vsm_int_quad μ β hββ W W i j).add h2).add h3).add (hεε i j)
  have hSyy : ∀ i j, ∫ ω, y ω i * y ω j ∂μ = (W * R * Wᵀ + Q) i j := by
    intro i j
    have e : (fun ω => y ω i * y ω j)
        = (fun ω => W.mulVec (β ω) i * W.mulVec (β ω) j
            + W.mulVec (β ω) i * ε ω j + ε ω i * W.mulVec (β ω) j + ε ω i * ε ω j) := by
      funext ω; rw [hy ω i, hy ω j]; ring
    have h2 : Integrable (fun ω => W.mulVec (β ω) i * ε ω j) μ :=
      vsm_int_lin_cross μ β ε hβε W i j
    have h3 : Integrable (fun ω => ε ω i * W.mulVec (β ω) j) μ := by
      have e3 : (fun ω => ε ω i * W.mulVec (β ω) j)
          = (fun ω => W.mulVec (β ω) j * ε ω i) := by funext ω; ring
      rw [e3]; exact vsm_int_lin_cross μ β ε hβε W j i
    have h1 : Integrable (fun ω => W.mulVec (β ω) i * W.mulVec (β ω) j) μ :=
      vsm_int_quad μ β hββ W W i j
    have h12 : Integrable (fun ω => W.mulVec (β ω) i * W.mulVec (β ω) j
        + W.mulVec (β ω) i * ε ω j) μ := h1.add h2
    have h123 : Integrable (fun ω => W.mulVec (β ω) i * W.mulVec (β ω) j
        + W.mulVec (β ω) i * ε ω j + ε ω i * W.mulVec (β ω) j) μ := h12.add h3
    rw [e, integral_add h123 (hεε i j), integral_add h12 h3, integral_add h1 h2]
    rw [vsm_quad_int μ β hββ R hR W W i j]
    rw [vsm_lin_cross_int μ β ε hβε 0 hSβε W i j]
    have h3' : (∫ ω, ε ω i * W.mulVec (β ω) j ∂μ) = 0 := by
      have e3 : (fun ω => ε ω i * W.mulVec (β ω) j)
          = (fun ω => W.mulVec (β ω) j * ε ω i) := by funext ω; ring
      rw [e3, vsm_lin_cross_int μ β ε hβε 0 hSβε W j i]
      simp
    rw [h3', hQ i j]
    simp [Matrix.add_apply]
  have hβy : ∀ (i : Fin n) (j : Fin m), Integrable (fun ω => β ω i * y ω j) μ := by
    intro i j
    have e : (fun ω => β ω i * y ω j)
        = (fun ω => W.mulVec (β ω) j * β ω i + β ω i * ε ω j) := by
      funext ω; rw [hy ω j]; ring
    rw [e]
    exact (vsm_int_lin_cross μ β β hββ W j i).add (hβε i j)
  have hSβy : ∀ i j, ∫ ω, β ω i * y ω j ∂μ = (R * Wᵀ) i j := by
    intro i j
    have e : (fun ω => β ω i * y ω j)
        = (fun ω => W.mulVec (β ω) j * β ω i + β ω i * ε ω j) := by
      funext ω; rw [hy ω j]; ring
    rw [e, integral_add (vsm_int_lin_cross μ β β hββ W j i) (hβε i j)]
    rw [vsm_lin_cross_int μ β β hββ R hR W j i, hSβε i j]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply, add_zero]
    exact Finset.sum_congr rfl fun k _ => by
      rw [show R k i = R i k from by rw [← Matrix.transpose_apply R i k, hRsymm]]
      ring
  have hK₀' : K₀ = (R * Wᵀ) * (W * R * Wᵀ + Q)⁻¹ := hK₀
  constructor
  · intro i
    exact vsm_mv_optimal μ y β hyy hβy hββ (W * R * Wᵀ + Q) hSyy (R * Wᵀ) hSβy R hR
      hdet K₀ hK₀' K i
  · intro i j
    rw [vsm_err_cov μ y β hyy hβy hββ (W * R * Wᵀ + Q) hSyy (R * Wᵀ) hSβy R hR K₀ i j]
    have hSsymm : (W * R * Wᵀ + Q)ᵀ = W * R * Wᵀ + Q := by
      ext a c
      rw [Matrix.transpose_apply, ← hSyy c a, ← hSyy a c]
      exact integral_congr_ae (Filter.Eventually.of_forall fun ω => mul_comm _ _)
    have hSinv : ((W * R * Wᵀ + Q)⁻¹)ᵀ = (W * R * Wᵀ + Q)⁻¹ := by
      rw [Matrix.transpose_nonsing_inv, hSsymm]
    have hK₀Syy : K₀ * (W * R * Wᵀ + Q) = R * Wᵀ := by
      rw [hK₀', Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.mul_one]
    have hT : R * Wᵀ * K₀ᵀ = R * Wᵀ * (W * R * Wᵀ + Q)⁻¹ * W * R := by
      rw [hK₀', Matrix.transpose_mul, hSinv, Matrix.transpose_mul, Matrix.transpose_transpose,
        hRsymm]
      simp only [Matrix.mul_assoc]
    have hU : K₀ * (R * Wᵀ)ᵀ = R * Wᵀ * (W * R * Wᵀ + Q)⁻¹ * W * R := by
      rw [hK₀', Matrix.transpose_mul, Matrix.transpose_transpose, hRsymm]
      simp only [Matrix.mul_assoc]
    have hV : K₀ * (W * R * Wᵀ + Q) * K₀ᵀ
        = R * Wᵀ * (W * R * Wᵀ + Q)⁻¹ * W * R := by
      rw [hK₀Syy, hT]
    rw [hT, hU, hV]
    simp only [Matrix.sub_apply]
    ring

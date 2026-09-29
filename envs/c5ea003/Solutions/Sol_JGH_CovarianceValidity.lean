-- Prove2me | solution 1 for JGH.CovarianceValidity
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-26T02:47:46.31098+00:00
-- url     : https://prove2.me/submissions/d898ea80-387b-47dd-93f2-d7989d0b2c6a

import Definitions.Def_JGH_NTK_Model
import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
Covariance well-definedness for Jacot--Gabriel--Hongler, arXiv:1806.07572v4,
Section 4.1, Proposition 1 (PDF p. 5), and Appendix A.1 (PDF pp. 11--12).
The coordinate map below extends Mathlib's Gaussian restriction lemma to repeated indices.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace ENNReal NNReal

namespace JGH

def coordinateMap {ι κ : Type*} [Fintype ι] [Fintype κ] (e : κ → ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ where
  toFun x := WithLp.toLp 2 (fun i ↦ x (e i))
  map_add' x y := by ext; simp
  map_smul' c x := by ext; simp

@[simp] lemma coordinateMap_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ → ι) (x : EuclideanSpace ℝ ι) (i : κ) : coordinateMap e x i = x (e i) := rfl

lemma measurePreserving_coordinateMap_multivariateGaussian {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {μ : EuclideanSpace ℝ ι} {S : Matrix ι ι ℝ}
    (hS : S.PosSemidef) (e : κ → ι) :
    MeasurePreserving (coordinateMap e) (multivariateGaussian μ S)
      (multivariateGaussian (coordinateMap e μ) (S.submatrix e e)) where
  measurable := by fun_prop
  map_eq := by
    apply IsGaussian.ext
    · simp only [id_eq, integral_id_multivariateGaussian]
      rw [ContinuousLinearMap.integral_id_map, integral_id_multivariateGaussian]
      exact IsGaussian.integrable_id
    rw [← ContinuousLinearMap.toBilinForm_inj]
    refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun κ ℝ).toBasis fun i j ↦ ?_
    rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
      covarianceBilin_apply_eq_cov, covariance_map]
    · have h (i : κ) : (fun u ↦ ⟪(EuclideanSpace.basisFun κ ℝ).toBasis i, u⟫) ∘
          coordinateMap e = fun u ↦ u (e i) := by ext; simp [PiLp.inner_apply]
      simp_rw [h, covariance_eval_multivariateGaussian hS,
        covarianceBilin_multivariateGaussian (hS.submatrix e)]
      simp
    any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
    · fun_prop
    · exact IsGaussian.memLp_two_id

lemma lipschitz_memLp_two {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : MemLp f 2 μ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) :
    MemLp (fun x ↦ σ (f x)) 2 μ := by
  have hs : LipschitzWith K (fun t ↦ σ t - σ 0) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    simpa using hσ.dist_le_mul x y
  have h := hs.comp_memLp (sub_self (σ 0)) hf
  convert h.add (memLp_const (σ 0)) using 1
  ext x
  simp

lemma activation_memLp_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : EuclideanSpace ℝ ι) (S : Matrix ι ι ℝ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (i : ι) :
    MemLp (fun x : EuclideanSpace ℝ ι ↦ σ (x i)) 2 (multivariateGaussian μ S) := by
  have h : MemLp (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2
      (multivariateGaussian μ S) := IsGaussian.memLp_two_id
  exact lipschitz_memLp_two
    (h.continuousLinearMap_comp (EuclideanSpace.proj (𝕜 := ℝ) i)) hσ

lemma integralGram_posSemidef {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} {f : ι → Ω → ℝ} (hf : ∀ i, MemLp (f i) 2 μ) :
    (Matrix.of (fun i j ↦ ∫ x, f i x * f j x ∂μ)).PosSemidef := by
  classical
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp [Matrix.conjTranspose_apply, mul_comm]
  · intro c
    simp only [dotProduct, mulVec, Pi.star_apply, star_trivial, Finset.mul_sum, Matrix.of_apply]
    have hprod (i j : ι) : Integrable (fun x ↦ c i * (f i x * f j x) * c j) μ :=
      ((hf i).integrable_mul (hf j)).const_mul (c i) |>.mul_const (c j)
    have hi : (∑ i, ∑ j, c i * (∫ x, f i x * f j x ∂μ) * c j) =
        ∫ x, ∑ i, ∑ j, c i * (f i x * f j x) * c j ∂μ := by
      rw [integral_finsetSum _ (fun i _ ↦ integrable_finsetSum _ (fun j _ ↦ hprod i j))]
      congr 1
      funext i
      rw [integral_finsetSum _ (fun j _ ↦ hprod i j)]
      simp only [integral_mul_const, integral_const_mul]
    simp only [← mul_assoc]
    rw [hi]
    apply integral_nonneg
    intro x
    change 0 ≤ ∑ i, ∑ j, c i * (f i x * f j x) * c j
    have he : (∑ i, ∑ j, c i * (f i x * f j x) * c j) =
        (∑ i, c i * f i x) ^ 2 := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [he]
    exact sq_nonneg _

lemma gaussianProductExpectation_posSemidef {d N : ℕ} {C : Kernel d}
    (X : Fin N → Input d)
    (hC : (Matrix.of (fun i j ↦ C (X i) (X j))).PosSemidef)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) :
    (Matrix.of (fun i j ↦ gaussianProductExpectation C σ (X i) (X j))).PosSemidef := by
  let S : Matrix (Fin N) (Fin N) ℝ := fun i j ↦ C (X i) (X j)
  let μ := multivariateGaussian 0 S
  have hcont : Continuous σ := hσ.continuous
  have hentry (i j : Fin N) : gaussianProductExpectation C σ (X i) (X j) =
      ∫ z : EuclideanSpace ℝ (Fin N), σ (z i) * σ (z j) ∂μ := by
    have hm : Measure.map (coordinateMap ![i, j]) μ = gaussianPair C (X i) (X j) := by
      have h := (measurePreserving_coordinateMap_multivariateGaussian
        (μ := (0 : EuclideanSpace ℝ (Fin N))) hC ![i, j]).map_eq
      convert h using 1
      simp only [gaussianPair, map_zero]
      congr 1
      ext a b
      fin_cases a <;> fin_cases b <;> rfl
    unfold gaussianProductExpectation
    rw [← hm, integral_map (by fun_prop) (by fun_prop)]
    simp only [coordinateMap_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp_rw [hentry]
  exact integralGram_posSemidef (fun i ↦ activation_memLp_two 0 S hσ i)

lemma constant_square_posSemidef {ι : Type*} [Finite ι] (β : ℝ) :
    (Matrix.of (fun _ _ : ι ↦ β ^ 2)).PosSemidef := by
  simpa only [vecMulVec, star_trivial, pow_two] using
    (Matrix.posSemidef_vecMulVec_self_star (fun _ : ι ↦ β))

lemma covarianceKernel_zero_posSemidef (d N : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) :
    (Matrix.of (fun i j ↦ covarianceKernel d σ β 0 (X i) (X j))).PosSemidef := by
  let A : Matrix (Fin d) (Fin N) ℝ := fun k i ↦ X i k
  have hA : (Matrix.of (fun i j ↦ ∑ k, X i k * X j k)).PosSemidef := by
    simpa [A, Matrix.mul_apply, Matrix.conjTranspose_apply] using
      (Matrix.posSemidef_conjTranspose_mul_self A)
  have h := hA.smul (a := (d : ℝ)⁻¹) (inv_nonneg.mpr (Nat.cast_nonneg d))
  simpa [covarianceKernel, Matrix.add_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using
    h.add (constant_square_posSemidef β)

lemma covarianceKernel_posSemidef (d : ℕ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (β : ℝ) (h N : ℕ) (X : Fin N → Input d) :
    (Matrix.of (fun i j ↦ covarianceKernel d σ β h (X i) (X j))).PosSemidef := by
  induction h generalizing N with
  | zero => exact covarianceKernel_zero_posSemidef d N σ β X
  | succ h ih =>
    have hG := gaussianProductExpectation_posSemidef X (ih N X) hσ
    simpa only [covarianceKernel, Matrix.of_apply, Matrix.add_apply] using
      hG.add (constant_square_posSemidef β)

lemma covarianceKernel_diagonal_lower (d : ℕ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (β : ℝ) (h : ℕ) (x : Input d) :
    β ^ 2 ≤ covarianceKernel d σ β h x x := by
  cases h with
  | zero =>
    apply le_add_of_nonneg_left
    apply div_nonneg
    · exact Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg (x i))
    · exact Nat.cast_nonneg d
  | succ h =>
    have hG := gaussianProductExpectation_posSemidef (fun _ : Fin 1 ↦ x)
      (covarianceKernel_posSemidef d hσ β h 1 (fun _ : Fin 1 ↦ x)) hσ
    exact le_add_of_nonneg_left (hG.diag_nonneg (i := 0))

end JGH


open MeasureTheory Filter
open scoped Topology NNReal

theorem solution :
    ∀ (d : ℕ), 0 < d → ∀ (σ : ℝ → ℝ) (K : ℝ≥0), LipschitzWith K σ →
      ∀ (β : ℝ), 0 < β → ∀ (h N : ℕ) (X : Fin N → JGH.Input d),
        (Matrix.of (fun i j ↦ JGH.covarianceKernel d σ β h (X i) (X j))).PosSemidef ∧
          ∀ x : JGH.Input d, β ^ 2 ≤ JGH.covarianceKernel d σ β h x x := by
  intro d _ σ K hσ β _ h N X
  exact ⟨JGH.covarianceKernel_posSemidef d hσ β h N X,
    JGH.covarianceKernel_diagonal_lower d hσ β h⟩

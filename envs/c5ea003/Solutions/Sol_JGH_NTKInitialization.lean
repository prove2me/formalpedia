-- Prove2me | solution 1 for JGH.NTKInitialization
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-26T03:44:31.077647+00:00
-- url     : https://prove2.me/submissions/7ddd3d9f-f490-426b-aa9a-bc6e9f55ff35

import Definitions.Def_JGH_NTK_Model
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Independence
import Mathlib.MeasureTheory.Measure.LevyConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Probability.StrongLaw
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.Analysis.Matrix.Order
import Mathlib.Topology.Neighborhoods
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.BoundedContinuousFunction
import Mathlib.MeasureTheory.Measure.TightNormed
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Analysis.Calculus.FDeriv.Equiv

/- Bundled from Definitions/JGH/NTKBase.lean. -/
/-!
The affine base of Jacot--Gabriel--Hongler Theorem 1, Appendix A.1, PDF p. 12
(arXiv:1806.07572v4). All weights and biases are differentiated explicitly.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal
namespace JGH

def affineOutputLinear (width : ℕ → ℕ) (β : ℝ) (x : Fin (width 0) → ℝ)
    (k : Fin (width 1)) : Parameters 1 width →L[ℝ] ℝ :=
  (Real.sqrt (width 0))⁻¹ •
    ∑ i, x i • ContinuousLinearMap.proj (⟨0, k, some i⟩ : ParameterIndex 1 width) +
      β • ContinuousLinearMap.proj (⟨0, k, none⟩ : ParameterIndex 1 width)

lemma network_one_eq_linear (width : ℕ → ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters 1 width) (x : Fin (width 0) → ℝ) (k : Fin (width 1)) :
    network 1 width σ β θ x k = affineOutputLinear width β x k θ := by
  simp [network, preactivation, affineOutputLinear, div_eq_inv_mul, mul_comm]

lemma parameterDerivative_one (width : ℕ → ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters 1 width) (x : Fin (width 0) → ℝ) (k j : Fin (width 1))
    (a : Option (Fin (width 0))) :
    parameterDerivative 1 width σ β θ x k ⟨0, j, a⟩ =
      if k = j then a.elim β (fun i ↦ x i / Real.sqrt (width 0)) else 0 := by
  classical
  unfold parameterDerivative
  simp_rw [network_one_eq_linear]
  rw [(affineOutputLinear width β x k).fderiv]
  cases a with
  | none =>
      by_cases hk : k = j
      · subst j
        simp [affineOutputLinear]
      · simp [affineOutputLinear, hk]
  | some i =>
      by_cases hk : k = j
      · subst j
        simp [affineOutputLinear, Pi.single_apply, div_eq_inv_mul]
      · simp [affineOutputLinear, hk]

lemma finiteNTK_one (width : ℕ → ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters 1 width) (x y : Fin (width 0) → ℝ) (k k' : Fin (width 1)) :
    finiteNTK 1 width σ β θ x y k k' =
      if k = k' then (∑ i, x i * y i) / width 0 + β ^ 2 else 0 := by
  classical
  unfold finiteNTK
  rw [Fintype.sum_sigma]
  simp only [Fin.sum_univ_one, Fintype.sum_prod_type, parameterDerivative_one]
  by_cases hkk : k = k'
  · subst k'
    simp only [ite_true]
    simp (config := { contextual := true }) [mul_ite, Finset.sum_ite_irrel]
    change (∑ a : Option (Fin (width 0)),
      (a.elim β (fun i ↦ x i / Real.sqrt (width 0))) *
      (a.elim β (fun i ↦ y i / Real.sqrt (width 0)))) = _
    rw [Fintype.sum_option]
    change β * β + (∑ i, (x i / Real.sqrt (width 0)) *
      (y i / Real.sqrt (width 0))) = _
    simp_rw [div_mul_div_comm, Real.mul_self_sqrt (Nat.cast_nonneg (width 0))]
    rw [← Finset.sum_div]
    ring
  · simp only [hkk, if_false]
    apply Finset.sum_eq_zero
    intro j _
    apply Finset.sum_eq_zero
    intro a _
    by_cases hk : k = j
    · have hk' : k' ≠ j := fun he ↦ hkk (hk.trans he.symm)
      simp [hk, hk']
    · simp [hk]

lemma finiteNTK_widths_zero (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (w : Fin 0 → ℕ) (θ : Parameters 1 (widths d q w)) (x y : Input d)
    (k k' : Fin q) :
    finiteNTK 1 (widths d q w) σ β θ
      (inputForWidths d q w x) (inputForWidths d q w y)
      (outputForWidths d q w k) (outputForWidths d q w k') =
      if k = k' then limitingNTK d σ β 0 x y else 0 := by
  simpa [widths, inputForWidths, outputForWidths, limitingNTK, covarianceKernel] using
    finiteNTK_one (widths d q w) σ β θ (inputForWidths d q w x)
      (inputForWidths d q w y) (outputForWidths d q w k) (outputForWidths d q w k')

lemma ntkBadProbability_zero {N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) {ε : ℝ} (hε : 0 < ε) (w : Fin 0 → ℕ) :
    ntkBadProbability d q σ β X ε w = 0 := by
  unfold ntkBadProbability
  simp [finiteNTK_widths_zero, not_lt.mpr hε.le]

theorem ntkInitialization_zero {N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (ntkBadProbability (h := 0) d q σ β X ε) (sequentialWidths 0) (𝓝 0) := by
  have he : ntkBadProbability (h := 0) d q σ β X ε = fun _ ↦ 0 :=
    funext (ntkBadProbability_zero d q σ β X hε)
  rw [he]
  exact tendsto_const_nhds

end JGH

end

/- Bundled from Definitions/JGH/GaussianInitialization.lean. -/
/-!
Initialization-law infrastructure for Jacot--Gabriel--Hongler, arXiv:1806.07572v4,
Appendix A.1, PDF pp. 11--12, Proposition 1 (unnumbered displays).
The continuity lemmas justify the measurability of the finite-network random vectors.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Matrix BoundedContinuousFunction
open scoped BigOperators Topology ENNReal NNReal
open scoped Matrix.Norms.L2Operator

namespace JGH

theorem continuous_preactivation_parameters (L : ℕ) (width : ℕ → ℕ)
    {σ : ℝ → ℝ} (hσ : Continuous σ) (β : ℝ) (x : Fin (width 0) → ℝ)
    (l : ℕ) (j : Fin (width l)) :
    Continuous (fun θ : Parameters L width ↦ preactivation L width σ β θ x l j) := by
  induction l with
  | zero => exact continuous_const
  | succ l ih =>
      simp only [preactivation]
      by_cases hl : l < L
      · simp only [dif_pos hl]
        apply Continuous.add
        · apply Continuous.div_const
          apply continuous_finsetSum
          intro i _
          apply Continuous.mul (continuous_apply _)
          by_cases hz : l = 0
          · simpa only [if_pos hz] using ih i
          · simpa only [if_neg hz] using hσ.comp (ih i)
        · exact continuous_const.mul (continuous_apply _)
      · simpa only [dif_neg hl] using
          (continuous_const : Continuous (fun _ : Parameters L width ↦ (0 : ℝ)))

theorem continuous_initializedOutput {h N : ℕ} (d q : ℕ) {σ : ℝ → ℝ}
    (hσ : Continuous σ) (β : ℝ) (X : Fin N → Input d) (w : Fin h → ℕ) :
    Continuous (initializedOutput d q σ β X w) := by
  apply (PiLp.continuous_toLp 2 (fun _ : Fin N × Fin q ↦ ℝ)).comp
  apply continuous_pi
  intro a
  exact continuous_preactivation_parameters _ _ hσ _ _ _ _

theorem measurable_initializedOutput {h N : ℕ} (d q : ℕ) {σ : ℝ → ℝ}
    {K : ℝ≥0} (hσ : LipschitzWith K σ) (β : ℝ) (X : Fin N → Input d)
    (w : Fin h → ℕ) : Measurable (initializedOutput d q σ β X w) :=
  (continuous_initializedOutput d q hσ.continuous β X w).measurable

/-- A finite linear image of standard Gaussian coordinates has its Gram covariance. -/
theorem map_standardGaussian_matrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix κ ι ℝ) :
    (stdGaussian (EuclideanSpace ℝ ι)).map A.toEuclideanLin.toContinuousLinearMap =
      multivariateGaussian 0 (A * A.conjTranspose) := by
  apply IsGaussian.ext
  · simp only [id_eq]
    rw [ContinuousLinearMap.integral_id_map]
    · simp
    · exact IsGaussian.integrable_id
  ext x y
  rw [covarianceBilin_map IsGaussian.memLp_two_id, covarianceBilin_stdGaussian,
    covarianceBilin_multivariateGaussian (Matrix.posSemidef_self_mul_conjTranspose A)]
  rw [← LinearMap.adjoint_toContinuousLinearMap,
    ← Matrix.toEuclideanLin_conjTranspose_eq_adjoint]
  change inner ℝ (A.conjTranspose.toEuclideanLin x)
      (A.conjTranspose.toEuclideanLin y) = _
  simp only [Matrix.toLpLin_apply, PiLp.inner_apply, RCLike.inner_apply,
    starRingEnd_apply, star_trivial, Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
    Matrix.mul_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem map_gaussianPi_matrix {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (A : Matrix κ ι ℝ) :
    (Measure.pi (fun _ : ι ↦ gaussianReal 0 1)).map
        (fun z ↦ WithLp.toLp 2 (A *ᵥ z)) =
      multivariateGaussian 0 (A * A.conjTranspose) := by
  have hfun : (fun z ↦ WithLp.toLp 2 (A *ᵥ z)) =
      A.toEuclideanLin.toContinuousLinearMap ∘ WithLp.toLp 2 := rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop), map_pi_eq_stdGaussian]
  exact map_standardGaussian_matrix A

/-- Covariance convergence implies weak convergence of centered finite Gaussian laws. -/
theorem tendsto_multivariateGaussian_covariance {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ℕ → Matrix ι ι ℝ) (T : Matrix ι ι ℝ)
    (hS : ∀ n, (S n).PosSemidef) (hT : T.PosSemidef)
    (hST : ∀ i j, Tendsto (fun n ↦ S n i j) atTop (𝓝 (T i j))) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ ι))
      (fun n ↦ (⟨multivariateGaussian 0 (S n), inferInstance⟩ :
      ProbabilityMeasure (EuclideanSpace ℝ ι))) atTop
      (𝓝 ⟨multivariateGaussian 0 T, inferInstance⟩) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  simp_rw [ProbabilityMeasure.coe_mk, charFun_multivariateGaussian (hS _),
    charFun_multivariateGaussian hT]
  apply (Complex.continuous_exp.tendsto _).comp
  apply Tendsto.sub tendsto_const_nhds
  apply Tendsto.div_const
  apply (Complex.continuous_ofReal.tendsto _).comp
  simp only [Matrix.mulVec, dotProduct]
  apply tendsto_finsetSum
  intro i _
  apply Tendsto.const_mul
  apply tendsto_finsetSum
  intro j _
  exact (hST i j).mul_const (t j)

set_option maxHeartbeats 600000 in
theorem continuous_multivariateGaussian_covariance {ι : Type*} [Fintype ι]
    [DecidableEq ι] :
    Continuous (Y := ProbabilityMeasure (EuclideanSpace ℝ ι))
      (fun S : {S : Matrix ι ι ℝ // S.PosSemidef} ↦
      (⟨multivariateGaussian 0 S.1, inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ ι))) := by
  letI : FirstCountableTopology (Matrix ι ι ℝ) :=
    inferInstanceAs (FirstCountableTopology (ι → ι → ℝ))
  rw [continuous_iff_seqContinuous]
  intro S T hST
  apply tendsto_multivariateGaussian_covariance (fun n ↦ (S n).1) T.1
    (fun n ↦ (S n).2) T.2
  intro i j
  exact (((continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)).tendsto
    T).comp hST

set_option maxHeartbeats 600000 in
/-- This version also applies to the nested width filter, without a countability assumption. -/
theorem tendsto_multivariateGaussian_covariance_filter {α ι : Type*}
    [Fintype ι] [DecidableEq ι] {l : Filter α}
    (S : α → Matrix ι ι ℝ) (T : Matrix ι ι ℝ)
    (hS : ∀ n, (S n).PosSemidef) (hT : T.PosSemidef)
    (hST : ∀ i j, Tendsto (fun n ↦ S n i j) l (𝓝 (T i j))) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ ι))
      (fun n ↦ (⟨multivariateGaussian 0 (S n), inferInstance⟩ :
      ProbabilityMeasure (EuclideanSpace ℝ ι))) l
      (𝓝 ⟨multivariateGaussian 0 T, inferInstance⟩) := by
  let G : {S : Matrix ι ι ℝ // S.PosSemidef} → ProbabilityMeasure (EuclideanSpace ℝ ι) :=
    fun S ↦ ⟨multivariateGaussian 0 S.1, inferInstance⟩
  change Tendsto (fun n ↦ G ⟨S n, hS n⟩) l (𝓝 (G ⟨T, hT⟩))
  have h : Tendsto (fun n ↦ (⟨S n, hS n⟩ : {S : Matrix ι ι ℝ // S.PosSemidef})) l
      (𝓝 ⟨T, hT⟩) := by
    apply tendsto_subtype_rng.mpr
    change Tendsto (fun n ↦ (S n : ι → ι → ℝ)) l (𝓝 (T : ι → ι → ℝ))
    exact tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr fun j ↦ hST i j
  have hG : Continuous G := continuous_multivariateGaussian_covariance
  exact (hG.tendsto ⟨T, hT⟩).comp h

/-- The random covariance in Proposition 1 becomes deterministic in the outer width limit.
The conditional Gaussian law is expressed by its characteristic function, so this lemma does
not require a density for the limiting (possibly singular) multivariate Gaussian. -/
theorem tendsto_gaussian_mixture_of_covariance_ae {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] [DecidableEq ι] (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : ℕ → ProbabilityMeasure (EuclideanSpace ℝ ι))
    (S : ℕ → Ω → Matrix ι ι ℝ) (T : Matrix ι ι ℝ)
    (hS : ∀ n ω, (S n ω).PosSemidef) (hT : T.PosSemidef)
    (hSm : ∀ n i j, Measurable (fun ω ↦ S n ω i j))
    (hST : ∀ᵐ ω ∂P, ∀ i j, Tendsto (fun n ↦ S n ω i j) atTop (𝓝 (T i j)))
    (hchar : ∀ n t, charFun (ν n) t =
      ∫ ω, charFun (multivariateGaussian 0 (S n ω)) t ∂P) :
    Tendsto ν atTop (𝓝 (⟨multivariateGaussian 0 T, inferInstance⟩ :
      ProbabilityMeasure (EuclideanSpace ℝ ι))) := by
  apply ProbabilityMeasure.tendsto_iff_tendsto_charFun.mpr
  intro t
  simp_rw [hchar]
  have hm n : AEStronglyMeasurable
      (fun ω ↦ charFun (multivariateGaussian 0 (S n ω)) t) P := by
    simp_rw [charFun_multivariateGaussian (hS n _)]
    apply Measurable.aestronglyMeasurable
    simp only [Matrix.mulVec, dotProduct]
    fun_prop
  have hlim : ∀ᵐ ω ∂P, Tendsto
      (fun n ↦ charFun (multivariateGaussian 0 (S n ω)) t) atTop
      (𝓝 (charFun (multivariateGaussian 0 T) t)) := by
    filter_upwards [hST] with ω hω
    exact ProbabilityMeasure.tendsto_iff_tendsto_charFun.mp
      (tendsto_multivariateGaussian_covariance (fun n ↦ S n ω) T (fun n ↦ hS n ω)
        hT hω) t
  simpa using tendsto_integral_of_dominated_convergence (fun _ : Ω ↦ (1 : ℝ)) hm
    (integrable_const 1) (fun n ↦ Filter.Eventually.of_forall fun ω ↦
      norm_charFun_le_one (μ := multivariateGaussian 0 (S n ω)) t) hlim

/-- Fubini's theorem turns a conditional Gaussian law into the mixture identity. -/
theorem charFun_map_prod_of_conditional_law {Ω Λ ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Λ] [Fintype ι]
    (P : Measure Ω) (Q : Measure Λ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Ω × Λ → EuclideanSpace ℝ ι) (hF : Measurable F)
    (G : Ω → Measure (EuclideanSpace ℝ ι))
    (hG : ∀ ω, Q.map (fun z ↦ F (ω, z)) = G ω) (t : EuclideanSpace ℝ ι) :
    charFun ((P.prod Q).map F) t = ∫ ω, charFun (G ω) t ∂P := by
  have hi : Integrable (fun z ↦ innerProbChar t (F z)) (P.prod Q) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      ((innerProbChar t).continuous.measurable.comp hF).aestronglyMeasurable
    exact Filter.Eventually.of_forall fun z ↦ by simp [innerProbChar_apply]
  rw [charFun_eq_integral_innerProbChar,
    integral_map hF.aemeasurable (innerProbChar t).continuous.aestronglyMeasurable,
    integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [] with ω
  have hFω : Measurable (fun z ↦ F (ω, z)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [← hG ω, charFun_eq_integral_innerProbChar,
    integral_map hFω.aemeasurable
      (innerProbChar t).continuous.aestronglyMeasurable]

/-- The exact joint Gaussian law of the affine network, including shared-input covariance. -/
theorem map_initialization_affine {ι : Type*} [Fintype ι] [DecidableEq ι]
    (width : ℕ → ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : ι → Fin (width 0) → ℝ) (k : ι → Fin (width 1)) :
    (initialization 1 width).map
        (fun θ ↦ WithLp.toLp 2 (fun a ↦ network 1 width σ β θ (X a) (k a))) =
      multivariateGaussian 0 (fun a b ↦ if k a = k b then
        (∑ i, X a i * X b i) / width 0 + β ^ 2 else 0) := by
  classical
  let A : Matrix ι (ParameterIndex 1 width) ℝ := fun a p ↦
    affineOutputLinear width β (X a) (k a) (Pi.single p 1)
  have hA : (fun θ ↦ WithLp.toLp 2 (fun a ↦ network 1 width σ β θ (X a) (k a))) =
      (fun θ ↦ WithLp.toLp 2 (A *ᵥ θ)) := by
    funext θ
    congr 1
    funext a
    rw [network_one_eq_linear]
    change affineOutputLinear width β (X a) (k a) θ =
      ∑ p, affineOutputLinear width β (X a) (k a) (Pi.single p 1) * θ p
    have hθ : θ = ∑ p, θ p • Pi.single p (1 : ℝ) := by ext p; simp [Pi.single_apply]
    conv_lhs => rw [hθ]
    simp [mul_comm]
  have hAA : A * A.conjTranspose = fun a b ↦ if k a = k b then
      (∑ i, X a i * X b i) / width 0 + β ^ 2 else 0 := by
    ext a b
    have hb := finiteNTK_one width σ β (0 : Parameters 1 width) (X a) (X b) (k a) (k b)
    simpa only [finiteNTK, parameterDerivative, network_one_eq_linear,
      ContinuousLinearMap.fderiv, Matrix.mul_apply, Matrix.conjTranspose_apply,
      star_trivial, A] using hb
  rw [hA, initialization, map_gaussianPi_matrix, hAA]

theorem map_initializedOutput_zero {N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) (w : Fin 0 → ℕ) :
    (initialization 1 (widths d q w)).map (initializedOutput d q σ β X w) =
      outputGaussian d q σ β 0 X := by
  simpa [initializedOutput, outputGaussian, covarianceKernel, inputForWidths,
    outputForWidths, widths] using
    map_initialization_affine (widths d q w) σ β
      (fun a : Fin N × Fin q ↦ inputForWidths d q w (X a.1))
      (fun a : Fin N × Fin q ↦ outputForWidths d q w a.2)

/-- Proposition 1 at depth one is an exact equality in law, with no width limit. -/
theorem gaussianInitialization_zero {N : ℕ} (d q : ℕ) {σ : ℝ → ℝ}
    {K : ℝ≥0} (hσ : LipschitzWith K σ) (β : ℝ) (X : Fin N → Input d) :
    TendstoInDistribution (initializedOutput (h := 0) d q σ β X)
      (sequentialWidths 0) id (fun w ↦ initialization 1 (widths d q w))
      (outputGaussian d q σ β 0 X) where
  forall_aemeasurable w := (measurable_initializedOutput d q hσ β X w).aemeasurable
  tendsto := by
    simp only [map_initializedOutput_zero, Measure.map_id]
    exact tendsto_const_nhds

end JGH

end

/- Bundled from Definitions/JGH/Covariance.lean. -/
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

lemma gaussianProductExpectation_eq_integral_family {d N : ℕ} {C : Kernel d}
    (X : Fin N → Input d)
    (hC : (Matrix.of (fun i j ↦ C (X i) (X j))).PosSemidef)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (i j : Fin N) :
    gaussianProductExpectation C σ (X i) (X j) =
      ∫ z : EuclideanSpace ℝ (Fin N), σ (z i) * σ (z j)
        ∂multivariateGaussian 0 (Matrix.of (fun a b ↦ C (X a) (X b))) := by
  have hcont : Continuous σ := hσ.continuous
  have hm : Measure.map (coordinateMap ![i, j])
      (multivariateGaussian 0 (Matrix.of (fun a b ↦ C (X a) (X b)))) =
        gaussianPair C (X i) (X j) := by
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

end

/- Bundled from Definitions/JGH/GaussianLLN.lean. -/
/-!
The empirical covariance law of large numbers used in Jacot--Gabriel--Hongler,
arXiv:1806.07572v4, Appendix A.1, Proposition 1, PDF pp. 11--12.
The probability space is an explicit countable product of centered Gaussian vector laws.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal NNReal RealInnerProductSpace

namespace JGH

lemma iid_empirical_mean_tendsto_ae {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] {f : E → ℝ}
    (hf : Measurable f) (hint : Integrable f ν) :
    ∀ᵐ ω : ℕ → E ∂Measure.infinitePi (fun _ : ℕ ↦ ν),
      Tendsto (fun n : ℕ ↦ (∑ a ∈ Finset.range n, f (ω a)) / n)
        atTop (𝓝 (∫ z, f z ∂ν)) := by
  let μ := Measure.infinitePi (fun _ : ℕ ↦ ν)
  have hident (n : ℕ) : IdentDistrib (fun ω : ℕ → E ↦ f (ω n)) f μ ν := {
    aemeasurable_fst := (hf.comp (measurable_pi_apply n)).aemeasurable
    aemeasurable_snd := hf.aemeasurable
    map_eq := by
      change μ.map (f ∘ Function.eval n) = ν.map f
      rw [← Measure.map_map hf (by fun_prop)]
      exact congrArg (fun m : Measure E ↦ m.map f)
        (Measure.infinitePi_map_eval (fun _ : ℕ ↦ ν) n) }
  have hindep : iIndepFun (fun n (ω : ℕ → E) ↦ f (ω n)) μ :=
    iIndepFun_infinitePi (fun _ ↦ hf)
  have h := strong_law_ae_real (fun n (ω : ℕ → E) ↦ f (ω n))
    ((hident 0).integrable_iff.mpr hint) (fun i j hij ↦ hindep.indepFun hij)
    (fun n ↦ (hident n).trans (hident 0).symm)
  simpa only [(hident 0).integral_eq] using h

lemma gaussian_activation_empirical_covariance_tendsto_ae
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (i j : ι) :
    ∀ᵐ ω : ℕ → EuclideanSpace ℝ ι
        ∂Measure.infinitePi (fun _ : ℕ ↦ multivariateGaussian 0 S),
      Tendsto (fun n : ℕ ↦ (∑ a ∈ Finset.range (n + 1),
        σ (ω a i) * σ (ω a j)) / (n + 1 : ℕ)) atTop
        (𝓝 (∫ z : EuclideanSpace ℝ ι, σ (z i) * σ (z j)
          ∂multivariateGaussian 0 S)) := by
  have hc : Continuous σ := hσ.continuous
  have h := iid_empirical_mean_tendsto_ae (multivariateGaussian 0 S)
    (f := fun z ↦ σ (z i) * σ (z j)) (by fun_prop)
    ((activation_memLp_two 0 S hσ i).integrable_mul (activation_memLp_two 0 S hσ j))
  filter_upwards [h] with ω hω
  exact hω.comp (tendsto_add_atTop_nat 1)

lemma gaussian_activation_empirical_covariance_tendsto_ae_all
    {ι : Type*} [Fintype ι] [DecidableEq ι] (S : Matrix ι ι ℝ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) :
    ∀ᵐ ω : ℕ → EuclideanSpace ℝ ι
        ∂Measure.infinitePi (fun _ : ℕ ↦ multivariateGaussian 0 S), ∀ i j : ι,
      Tendsto (fun n : ℕ ↦ (∑ a ∈ Finset.range (n + 1),
        σ (ω a i) * σ (ω a j)) / (n + 1 : ℕ)) atTop
        (𝓝 (∫ z : EuclideanSpace ℝ ι, σ (z i) * σ (z j)
          ∂multivariateGaussian 0 S)) := by
  exact ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦
    gaussian_activation_empirical_covariance_tendsto_ae S hσ i j

lemma measurePreserving_iidPrefix {E : Type*} [MeasurableSpace E]
    (ν : Measure E) [IsProbabilityMeasure ν] (n : ℕ) :
    MeasurePreserving (fun (ω : ℕ → E) (a : Fin n) ↦ ω a)
      (Measure.infinitePi (fun _ : ℕ ↦ ν)) (Measure.pi (fun _ : Fin n ↦ ν)) where
  measurable := by fun_prop
  map_eq := by
    rw [Measure.map_infinitePi_infinitePi_of_inj (f := fun a : Fin n ↦ (a : ℕ))
      Fin.val_injective, Measure.infinitePi_eq_pi]

def empiricalActivationCovariance {ι : Type*} (σ : ℝ → ℝ) (β : ℝ)
    (n : ℕ) (ω : ℕ → EuclideanSpace ℝ ι) : Matrix ι ι ℝ :=
  fun i j ↦ (∑ a ∈ Finset.range (n + 1), σ (ω a i) * σ (ω a j)) /
    (n + 1 : ℕ) + β ^ 2

lemma empiricalActivationCovariance_posSemidef {ι : Type*} [Fintype ι]
    (σ : ℝ → ℝ) (β : ℝ) (n : ℕ) (ω : ℕ → EuclideanSpace ℝ ι) :
    (empiricalActivationCovariance σ β n ω).PosSemidef := by
  have hG : (∑ a ∈ Finset.range (n + 1),
      Matrix.of (fun i j ↦ σ (ω a i) * σ (ω a j))).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro a _
    simpa only [Matrix.vecMulVec, star_trivial] using
      Matrix.posSemidef_vecMulVec_self_star (fun i ↦ σ (ω a i))
  have h := hG.smul (a := ((n + 1 : ℕ) : ℝ)⁻¹)
    (inv_nonneg.mpr (Nat.cast_nonneg (n + 1)))
  convert h.add (constant_square_posSemidef β) using 1
  ext i j
  simp [empiricalActivationCovariance, Matrix.add_apply, Matrix.sum_apply,
    div_eq_mul_inv, smul_eq_mul, mul_comm]

lemma continuous_empiricalActivationCovariance {ι : Type*} [Fintype ι]
    {σ : ℝ → ℝ} (hσ : Continuous σ) (β : ℝ) (n : ℕ) :
    Continuous (empiricalActivationCovariance (ι := ι) σ β n) := by
  unfold empiricalActivationCovariance
  fun_prop

lemma measurable_empiricalActivationCovariance_entry {ι : Type*} [Fintype ι]
    {σ : ℝ → ℝ} (hσ : Continuous σ) (β : ℝ) (n : ℕ) (i j : ι) :
    Measurable (fun ω ↦ empiricalActivationCovariance σ β n ω i j) := by
  unfold empiricalActivationCovariance
  fun_prop

lemma expectedActivationCovariance_posSemidef {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : Matrix ι ι ℝ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (β : ℝ) :
    (Matrix.of (fun i j ↦ (∫ z : EuclideanSpace ℝ ι, σ (z i) * σ (z j)
      ∂multivariateGaussian 0 S) + β ^ 2)).PosSemidef := by
  exact (integralGram_posSemidef (fun i ↦ activation_memLp_two 0 S hσ i)).add
    (constant_square_posSemidef β)

lemma empiricalActivationCovariance_tendsto_ae {ι : Type*} [Fintype ι]
    [DecidableEq ι] (S : Matrix ι ι ℝ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (β : ℝ) :
    ∀ᵐ ω : ℕ → EuclideanSpace ℝ ι
        ∂Measure.infinitePi (fun _ : ℕ ↦ multivariateGaussian 0 S),
      Tendsto (fun n ↦ empiricalActivationCovariance σ β n ω) atTop
        (𝓝 (fun i j ↦ (∫ z : EuclideanSpace ℝ ι, σ (z i) * σ (z j)
          ∂multivariateGaussian 0 S) + β ^ 2)) := by
  filter_upwards [gaussian_activation_empirical_covariance_tendsto_ae_all S hσ] with ω hω
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  exact (hω i j).add_const (β ^ 2)

def gaussianColumnsMap {ι κ : Type*} [Fintype ι] [Fintype κ] :
    (κ → EuclideanSpace ℝ ι) →L[ℝ] EuclideanSpace ℝ (ι × κ) where
  toFun Z := WithLp.toLp 2 (fun a ↦ Z a.2 a.1)
  map_add' X Y := by ext; simp
  map_smul' c X := by ext; simp

@[simp] lemma gaussianColumnsMap_apply {ι κ : Type*} [Fintype ι] [Fintype κ]
    (Z : κ → EuclideanSpace ℝ ι) (a : ι × κ) : gaussianColumnsMap Z a = Z a.2 a.1 := rfl

lemma blockCovariance_posSemidef {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    (Matrix.of (fun a b : ι × κ ↦ if a.2 = b.2 then C a.1 b.1 else 0)).PosSemidef := by
  convert hC.kronecker (Matrix.PosSemidef.one : (1 : Matrix κ κ ℝ).PosSemidef) using 1
  ext a b
  simp [Matrix.one_apply, mul_ite]

lemma gaussianColumns_pi_isGaussian {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] (C : Matrix ι ι ℝ) :
    IsGaussian (Measure.pi (fun _ : κ ↦ multivariateGaussian 0 C)) := by
  let μ := Measure.pi (fun _ : κ ↦ multivariateGaussian 0 C)
  have hX (k : κ) : HasGaussianLaw (fun Z : κ → EuclideanSpace ℝ ι ↦ Z k) μ := {
    isGaussian_map := by
      rw [(measurePreserving_eval (fun _ : κ ↦ multivariateGaussian 0 C) k).map_eq]
      infer_instance }
  have hindep : iIndepFun (fun k (Z : κ → EuclideanSpace ℝ ι) ↦ Z k) μ :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have h := hindep.hasGaussianLaw hX
  have hi : IsGaussian (μ.map id) := h.isGaussian_map
  simpa only [Measure.map_id] using hi

lemma covariance_gaussianColumns {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (a b : ι × κ) :
    cov[fun Z : κ → EuclideanSpace ℝ ι ↦ Z a.2 a.1,
      fun Z : κ → EuclideanSpace ℝ ι ↦ Z b.2 b.1;
      Measure.pi (fun _ : κ ↦ multivariateGaussian 0 C)] =
        if a.2 = b.2 then C a.1 b.1 else 0 := by
  let μ := Measure.pi (fun _ : κ ↦ multivariateGaussian 0 C)
  have hmem (a : ι × κ) : MemLp (fun Z : κ → EuclideanSpace ℝ ι ↦ Z a.2 a.1) 2 μ := by
    have heval : MemLp (fun z : EuclideanSpace ℝ ι ↦ z a.1) 2
        (multivariateGaussian 0 C) := by
      simpa using activation_memLp_two 0 C LipschitzWith.id a.1
    exact heval.comp_measurePreserving
      (measurePreserving_eval (fun _ : κ ↦ multivariateGaussian 0 C) a.2)
  by_cases hab : a.2 = b.2
  · rw [if_pos hab]
    have h := covariance_map_fun (μ := μ)
      (X := fun z : EuclideanSpace ℝ ι ↦ z a.1)
      (Y := fun z : EuclideanSpace ℝ ι ↦ z b.1)
      (Z := fun Z : κ → EuclideanSpace ℝ ι ↦ Z b.2)
      (by fun_prop) (by fun_prop) (measurable_pi_apply b.2).aemeasurable
    rw [(measurePreserving_eval (fun _ : κ ↦ multivariateGaussian 0 C) b.2).map_eq,
      covariance_eval_multivariateGaussian hC] at h
    simpa only [hab] using h.symm
  · rw [if_neg hab]
    have hindep : iIndepFun (fun k (Z : κ → EuclideanSpace ℝ ι) ↦ Z k) μ :=
      iIndepFun_pi (fun _ ↦ aemeasurable_id)
    have hh := (hindep.indepFun hab).comp
      (show Measurable (fun z : EuclideanSpace ℝ ι ↦ z a.1) by fun_prop)
      (show Measurable (fun z : EuclideanSpace ℝ ι ↦ z b.1) by fun_prop)
    exact hh.covariance_eq_zero (hmem a) (hmem b)

lemma map_gaussianColumns {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    (Measure.pi (fun _ : κ ↦ multivariateGaussian 0 C)).map gaussianColumnsMap =
      multivariateGaussian 0
        (fun a b : ι × κ ↦ if a.2 = b.2 then C a.1 b.1 else 0) := by
  let μ := Measure.pi (fun _ : κ ↦ multivariateGaussian 0 C)
  letI : IsGaussian μ := gaussianColumns_pi_isGaussian C
  have hmean : (∫ Z : κ → EuclideanSpace ℝ ι, Z ∂μ) = 0 := by
    have hint (k : κ) : Integrable (fun Z : κ → EuclideanSpace ℝ ι ↦ Z k) μ :=
      integrable_eval IsGaussian.integrable_id
    funext k
    rw [eval_integral hint, integral_eval, integral_id_multivariateGaussian]
    rfl
  apply IsGaussian.ext
  · simp only [id_eq, integral_id_multivariateGaussian]
    rw [ContinuousLinearMap.integral_id_map]
    · rw [hmean, map_zero]
    · exact IsGaussian.integrable_id
  rw [← ContinuousLinearMap.toBilinForm_inj]
  refine LinearMap.BilinForm.ext_basis (EuclideanSpace.basisFun (ι × κ) ℝ).toBasis
    fun a b ↦ ?_
  rw [ContinuousLinearMap.toBilinForm_apply, ContinuousLinearMap.toBilinForm_apply,
    covarianceBilin_apply_eq_cov, covariance_map]
  · have h (a : ι × κ) : (fun u ↦ ⟪(EuclideanSpace.basisFun (ι × κ) ℝ).toBasis a, u⟫) ∘
        gaussianColumnsMap = fun Z : κ → EuclideanSpace ℝ ι ↦ Z a.2 a.1 := by
      ext Z
      simp [PiLp.inner_apply]
    simp_rw [h, covariance_gaussianColumns hC]
    have hB : Matrix.PosSemidef
        (fun a b : ι × κ ↦ if a.2 = b.2 then C a.1 b.1 else 0) :=
      blockCovariance_posSemidef hC
    rw [covarianceBilin_multivariateGaussian hB]
    simp
  any_goals exact Measurable.aestronglyMeasurable (by fun_prop)
  · fun_prop
  · exact IsGaussian.memLp_two_id

end JGH

end

/- Bundled from Definitions/JGH/SequentialLimits.lean. -/
/-!
Filter bridges for the sequential width convention of Jacot--Gabriel--Hongler,
Appendix A opening paragraphs, PDF p. 11 (arXiv:1806.07572v4).
These arguments require no countable generation of the nested-tail filter.
-/

open Filter
open scoped Topology
namespace JGH

instance sequentialWidths_neBot (h : ℕ) : (sequentialWidths h).NeBot := by
  induction h with
  | zero => change (pure Fin.elim0 : Filter (Fin 0 → ℕ)).NeBot; infer_instance
  | succ h ih =>
      letI := ih
      rw [← Filter.frequently_true_iff_neBot]
      simp only [sequentialWidths, Filter.frequently_bind, Filter.frequently_map]
      simpa using ih

theorem tendsto_sequentialWidths_succ {E : Type*} [TopologicalSpace E]
    {h : ℕ} {f : (Fin (h + 1) → ℕ) → E} {g : ℕ → E} {a : E}
    (hinner : ∀ n, Tendsto (fun w ↦ f (Fin.snoc w n)) (sequentialWidths h) (𝓝 (g n)))
    (houter : Tendsto g atTop (𝓝 a)) :
    Tendsto f (sequentialWidths (h + 1)) (𝓝 a) := by
  change map f (atTop.bind fun n ↦ (sequentialWidths h).map (fun w ↦ Fin.snoc w n)) ≤ 𝓝 a
  rw [map_bind]
  simp only [map_map, Function.comp_def]
  calc
    _ ≤ atTop.bind (fun n ↦ 𝓝 (g n)) := bind_mono le_rfl (Eventually.of_forall hinner)
    _ = (map g atTop).bind (fun b ↦ 𝓝 b) := (bind_map g atTop _).symm
    _ ≤ (𝓝 a).bind (fun b ↦ 𝓝 b) := bind_mono houter (Eventually.of_forall fun _ ↦ le_rfl)
    _ = 𝓝 a := nhds_bind_nhds

end JGH

/- Bundled from Definitions/JGH/LayerSplit.lean. -/
/-!
Parameter splitting in Jacot--Gabriel--Hongler, Appendix A.1, PDF pp. 12–13.
The last affine layer has its own independent standard Gaussian coordinates.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
namespace JGH

def affineLayerWidth (L : ℕ) (width : ℕ → ℕ) (l : ℕ) : ℕ :=
  if l = 0 then width L else width (L + 1)

def parameterIndexSplit (L : ℕ) (width : ℕ → ℕ) :
    ParameterIndex L width ⊕ ParameterIndex 1 (affineLayerWidth L width) ≃
      ParameterIndex (L + 1) width where
  toFun p := match p with
    | Sum.inl ⟨l, a⟩ => ⟨l.castSucc, a⟩
    | Sum.inr ⟨l, a⟩ => by
        have hl : l = 0 := Subsingleton.elim _ _
        subst l
        exact ⟨Fin.last L, a⟩
  invFun p := Fin.lastCases
    (fun a ↦ Sum.inr (⟨0, a⟩ : ParameterIndex 1 (affineLayerWidth L width)))
    (fun l a ↦ Sum.inl (⟨l, a⟩ : ParameterIndex L width)) p.1 p.2
  left_inv p := by
    rcases p with ⟨l, a⟩ | ⟨l, a⟩
    · simp
    · have hl : l = 0 := Subsingleton.elim _ _
      subst l
      simp
  right_inv p := by
    rcases p with ⟨l, a⟩
    revert a
    refine Fin.lastCases ?_ (fun l ↦ ?_) l
    · intro a
      simp
    · intro a
      simp

def splitParameters (L : ℕ) (width : ℕ → ℕ) :
    Parameters (L + 1) width ≃ᵐ
      (Parameters L width × Parameters 1 (affineLayerWidth L width)) :=
  (MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) (parameterIndexSplit L width).symm).trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ ↦ ℝ))

theorem measurePreserving_splitParameters (L : ℕ) (width : ℕ → ℕ) :
    MeasurePreserving (splitParameters L width) (initialization (L + 1) width)
      ((initialization L width).prod (initialization 1 (affineLayerWidth L width))) := by
  exact (measurePreserving_sumPiEquivProdPi (fun _ ↦ gaussianReal 0 1)).comp
    (measurePreserving_piCongrLeft (fun _ ↦ gaussianReal 0 1) (parameterIndexSplit L width).symm)

@[simp] theorem splitParameters_fst (L : ℕ) (width : ℕ → ℕ)
    (θ : Parameters (L + 1) width) (l : Fin L)
    (a : Fin (width (l.val + 1)) × Option (Fin (width l.val))) :
    (splitParameters L width θ).1 ⟨l, a⟩ = θ ⟨l.castSucc, a⟩ := by
  simp [splitParameters, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft', MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
    parameterIndexSplit]


@[simp] theorem splitParameters_snd (L : ℕ) (width : ℕ → ℕ)
    (θ : Parameters (L + 1) width)
    (a : Fin (width (L + 1)) × Option (Fin (width L))) :
    (splitParameters L width θ).2 ⟨0, a⟩ = θ ⟨Fin.last L, a⟩ := by
  simp [splitParameters, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft', MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
    parameterIndexSplit]

theorem preactivation_split_prefix (L : ℕ) (width : ℕ → ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters (L + 1) width) (x : Fin (width 0) → ℝ) (k : ℕ) (hk : k ≤ L) :
    preactivation (L + 1) width σ β θ x k =
      preactivation L width σ β (splitParameters L width θ).1 x k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      have hk' : k < L := hk
      have hkl : k < L + 1 := Nat.lt_trans hk' (Nat.lt_succ_self L)
      funext j
      simp only [preactivation, dif_pos hk', dif_pos hkl, splitParameters_fst,
        ih (Nat.le_of_lt hk')]
      rfl

theorem network_split_last (L : ℕ) (hL : 0 < L) (width : ℕ → ℕ)
    (σ : ℝ → ℝ) (β : ℝ) (θ : Parameters (L + 1) width)
    (x : Fin (width 0) → ℝ) (k : Fin (width (L + 1))) :
    network (L + 1) width σ β θ x k =
      network 1 (affineLayerWidth L width) σ β (splitParameters L width θ).2
        (fun i ↦ σ (network L width σ β (splitParameters L width θ).1 x i)) k := by
  simp [network, preactivation, Nat.ne_of_gt hL,
    preactivation_split_prefix L width σ β θ x L le_rfl, affineLayerWidth,
    splitParameters, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft', MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
    parameterIndexSplit]
  rfl

theorem widths_snoc_le {h : ℕ} (d q : ℕ) (w : Fin h → ℕ) (n l : ℕ)
    (hl : l ≤ h + 1) :
    widths d q (Fin.snoc w n) l = widths d (n + 1) w l := by
  by_cases hz : l = 0
  · simp [widths, hz]
  by_cases he : l = h + 1
  · subst l
    simp [widths]
    exact @Fin.snoc_last h (fun _ ↦ ℕ) n w
  have hi : l - 1 < h := by omega
  have hi' : l - 1 < h + 1 := by omega
  simp only [widths, if_neg hz, dif_pos hi, dif_pos hi']
  have hfin : (⟨l - 1, hi'⟩ : Fin (h + 1)) = (⟨l - 1, hi⟩ : Fin h).castSucc := rfl
  rw [hfin, Fin.snoc_castSucc]

end JGH

end

/- Bundled from Definitions/JGH/WidthTransport.lean. -/
/-! Width transport for the finite-layer decomposition in Jacot--Gabriel--Hongler,
Appendix A.1, PDF pp. 11--12. Only widths through the network's last layer matter. -/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace JGH

def parameterIndexWidthEquiv {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) : ParameterIndex L v ≃ ParameterIndex L w :=
  Equiv.sigmaCongrRight fun l ↦
    Equiv.prodCongr (finCongr (hvw (l.val + 1) l.isLt))
      (Equiv.optionCongr (finCongr (hvw l.val (Nat.le_of_lt l.isLt))))

def transportParameters {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) : Parameters L v ≃ᵐ Parameters L w :=
  MeasurableEquiv.piCongrLeft (fun _ ↦ ℝ) (parameterIndexWidthEquiv hvw)

theorem measurePreserving_transportParameters {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) :
    MeasurePreserving (transportParameters hvw) (initialization L v) (initialization L w) :=
  measurePreserving_piCongrLeft (fun _ ↦ gaussianReal 0 1) (parameterIndexWidthEquiv hvw)

@[simp] theorem transportParameters_apply {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) (θ : Parameters L v) (l : Fin L)
    (j : Fin (v (l.val + 1))) (i : Option (Fin (v l.val))) :
    transportParameters hvw θ
      ⟨l, Fin.cast (hvw (l.val + 1) l.isLt) j,
        i.map (Fin.cast (hvw l.val (Nat.le_of_lt l.isLt)))⟩ = θ ⟨l, j, i⟩ := by
  have hp : parameterIndexWidthEquiv hvw ⟨l, j, i⟩ =
      ⟨l, Fin.cast (hvw (l.val + 1) l.isLt) j,
        i.map (Fin.cast (hvw l.val (Nat.le_of_lt l.isLt)))⟩ := by
    cases i <;> rfl
  rw [← hp]
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ ↦ ℝ)
    (parameterIndexWidthEquiv hvw) θ ⟨l, j, i⟩

@[simp] theorem transportParameters_weight {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) (θ : Parameters L v) (l : Fin L)
    (j : Fin (v (l.val + 1))) (i : Fin (v l.val)) :
    transportParameters hvw θ
      ⟨l, Fin.cast (hvw (l.val + 1) l.isLt) j,
        some (Fin.cast (hvw l.val (Nat.le_of_lt l.isLt)) i)⟩ = θ ⟨l, j, some i⟩ := by
  simpa using transportParameters_apply hvw θ l j (some i)

@[simp] theorem transportParameters_bias {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) (θ : Parameters L v) (l : Fin L)
    (j : Fin (v (l.val + 1))) :
    transportParameters hvw θ ⟨l, Fin.cast (hvw (l.val + 1) l.isLt) j, none⟩ =
      θ ⟨l, j, none⟩ := by
  simpa using transportParameters_apply hvw θ l j none

theorem preactivation_transport {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters L v) (x : Fin (v 0) → ℝ) (l : ℕ) (hl : l ≤ L) (j : Fin (v l)) :
    preactivation L w σ β (transportParameters hvw θ)
      (fun i ↦ x (Fin.cast (hvw 0 (Nat.zero_le L)).symm i)) l
        (Fin.cast (hvw l hl) j) = preactivation L v σ β θ x l j := by
  induction l with
  | zero => simp [preactivation]
  | succ l ih =>
      have hlt : l < L := hl
      have hle : l ≤ L := Nat.le_of_lt hlt
      simp only [preactivation, dif_pos hlt]
      rw [← (finCongr (hvw l hle)).sum_comp]
      simp only [finCongr_apply, transportParameters_weight, transportParameters_bias,
        hvw l hle, ih hle]

theorem network_transport {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters L v) (x : Fin (v 0) → ℝ) (j : Fin (v L)) :
    network L w σ β (transportParameters hvw θ)
      (fun i ↦ x (Fin.cast (hvw 0 (Nat.zero_le L)).symm i))
        (Fin.cast (hvw L le_rfl) j) = network L v σ β θ x j :=
  preactivation_transport hvw σ β θ x L le_rfl j

theorem network_transport_apply {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters L v) (x : Fin (v 0) → ℝ) (j : Fin (w L)) :
    network L w σ β (transportParameters hvw θ)
      (fun i ↦ x (Fin.cast (hvw 0 (Nat.zero_le L)).symm i)) j =
      network L v σ β θ x (Fin.cast (hvw L le_rfl).symm j) := by
  simpa using network_transport hvw σ β θ x (Fin.cast (hvw L le_rfl).symm j)

end JGH

end

/- Bundled from Definitions/JGH/GaussianLimit.lean. -/
/-!
Proof development for Jacot--Gabriel--Hongler Proposition 1, Appendix A.1,
PDF pp. 11--12, arXiv:1806.07572v4. The affine base and outer-width limit are
assembled from exact Gaussian laws and the empirical covariance strong law.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators Topology ENNReal NNReal
namespace JGH

def upperLayer {N : ℕ} (n q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin n) × Parameters 1 (widths n q Fin.elim0)) :
    EuclideanSpace ℝ (Fin N × Fin q) :=
  initializedOutput n q σ β (fun i j ↦ σ (z.1 (i, j))) Fin.elim0 z.2

theorem continuous_upperLayer {N : ℕ} (n q : ℕ) {σ : ℝ → ℝ}
    (hσ : Continuous σ) (β : ℝ) : Continuous (upperLayer (N := N) n q σ β) := by
  unfold upperLayer initializedOutput network
  apply (PiLp.continuous_toLp 2 (fun _ : Fin N × Fin q ↦ ℝ)).comp
  apply continuous_pi
  intro a
  simp [preactivation, inputForWidths, outputForWidths, widths]
  fun_prop

def upperLayerCovariance {N : ℕ} (n q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin n)) : Matrix (Fin N × Fin q) (Fin N × Fin q) ℝ :=
  fun a b ↦ if a.2 = b.2 then
    (∑ i : Fin n, σ (z (a.1, i)) * σ (z (b.1, i))) / n + β ^ 2 else 0

theorem map_upperLayer_section {N : ℕ} (n q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin n)) :
    (initialization 1 (widths n q Fin.elim0)).map (fun θ ↦ upperLayer n q σ β (z, θ)) =
      multivariateGaussian 0 (upperLayerCovariance n q σ β z) := by
  exact map_initializedOutput_zero n q σ β (fun i j ↦ σ (z (i, j))) Fin.elim0

theorem upperLayerCovariance_posSemidef {N : ℕ} (n q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (z : EuclideanSpace ℝ (Fin N × Fin n)) :
    (upperLayerCovariance n q σ β z).PosSemidef := by
  unfold upperLayerCovariance
  apply blockCovariance_posSemidef (C := fun i j ↦
    (∑ k : Fin n, σ (z (i, k)) * σ (z (j, k))) / n + β ^ 2)
  have hG : (∑ k : Fin n, Matrix.of (fun i j : Fin N ↦
      σ (z (i, k)) * σ (z (j, k)))).PosSemidef := by
    apply Matrix.posSemidef_sum
    intro k _
    simpa only [Matrix.vecMulVec, star_trivial] using
      Matrix.posSemidef_vecMulVec_self_star (fun i ↦ σ (z (i, k)))
  convert (hG.smul (a := ((n : ℝ)⁻¹)) (inv_nonneg.mpr (Nat.cast_nonneg n))).add
    (constant_square_posSemidef β) using 1
  ext i j
  simp [Matrix.add_apply, Matrix.sum_apply, div_eq_mul_inv, smul_eq_mul, mul_comm]

def gaussianUpperLaw {N : ℕ} (C : Matrix (Fin N) (Fin N) ℝ)
    (n q : ℕ) (σ : ℝ → ℝ) (hσ : Continuous σ) (β : ℝ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin N × Fin q)) :=
  ProbabilityMeasure.map (⟨(multivariateGaussian 0 (fun a b : Fin N × Fin n ↦
      if a.2 = b.2 then C a.1 b.1 else 0)).prod
        (initialization 1 (widths n q Fin.elim0)), inferInstance⟩ :
      ProbabilityMeasure (EuclideanSpace ℝ (Fin N × Fin n) ×
        Parameters 1 (widths n q Fin.elim0)))
    (continuous_upperLayer n q hσ β).measurable.aemeasurable

theorem measurePreserving_gaussianPrefix {N : ℕ}
    (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef) (n : ℕ) :
    MeasurePreserving (fun ω : ℕ → EuclideanSpace ℝ (Fin N) ↦
      gaussianColumnsMap (fun a : Fin n ↦ ω a))
      (Measure.infinitePi (fun _ : ℕ ↦ multivariateGaussian 0 C))
      (multivariateGaussian 0 (fun a b : Fin N × Fin n ↦
        if a.2 = b.2 then C a.1 b.1 else 0)) :=
  (show MeasurePreserving gaussianColumnsMap
      (Measure.pi (fun _ : Fin n ↦ multivariateGaussian 0 C))
      (multivariateGaussian 0 (fun a b : Fin N × Fin n ↦
        if a.2 = b.2 then C a.1 b.1 else 0)) from
      ⟨(gaussianColumnsMap (ι := Fin N) (κ := Fin n)).measurable,
        map_gaussianColumns hC⟩).comp
    (measurePreserving_iidPrefix (multivariateGaussian 0 C) n)

theorem upperLayerCovariance_gaussianPrefix {N : ℕ} (n q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (ω : ℕ → EuclideanSpace ℝ (Fin N)) :
    upperLayerCovariance (n + 1) q σ β
      (gaussianColumnsMap (fun a : Fin (n + 1) ↦ ω a)) =
      fun a b : Fin N × Fin q ↦ if a.2 = b.2 then
        empiricalActivationCovariance σ β n ω a.1 b.1 else 0 := by
  ext a b
  simp only [upperLayerCovariance, gaussianColumnsMap_apply, empiricalActivationCovariance]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ σ (ω k a.1) * σ (ω k b.1))]

theorem gaussianUpperLaw_tendsto {N : ℕ} (C : Matrix (Fin N) (Fin N) ℝ)
    (hC : C.PosSemidef) (q : ℕ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (β : ℝ) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (Fin N × Fin q)))
      (fun n ↦ gaussianUpperLaw C (n + 1) q σ hσ.continuous β) atTop
      (𝓝 ⟨multivariateGaussian 0 (fun a b : Fin N × Fin q ↦
        if a.2 = b.2 then
          (∫ z : EuclideanSpace ℝ (Fin N), σ (z a.1) * σ (z b.1)
            ∂multivariateGaussian 0 C) + β ^ 2 else 0), inferInstance⟩) := by
  let P := Measure.infinitePi (fun _ : ℕ ↦ multivariateGaussian 0 C)
  let S := fun n (ω : ℕ → EuclideanSpace ℝ (Fin N)) (a b : Fin N × Fin q) ↦
    if a.2 = b.2 then empiricalActivationCovariance σ β n ω a.1 b.1 else 0
  let T := fun a b : Fin N × Fin q ↦ if a.2 = b.2 then
    (∫ z : EuclideanSpace ℝ (Fin N), σ (z a.1) * σ (z b.1)
      ∂multivariateGaussian 0 C) + β ^ 2 else 0
  have hc : Continuous σ := hσ.continuous
  apply tendsto_gaussian_mixture_of_covariance_ae P
    (fun n ↦ gaussianUpperLaw C (n + 1) q σ hσ.continuous β) S T
    (fun n ω ↦ blockCovariance_posSemidef
      (empiricalActivationCovariance_posSemidef σ β n ω))
    (blockCovariance_posSemidef (expectedActivationCovariance_posSemidef C hσ β))
  · intro n a b
    dsimp [S]
    split_ifs
    · exact measurable_empiricalActivationCovariance_entry hc β n a.1 b.1
    · exact measurable_const
  · filter_upwards [empiricalActivationCovariance_tendsto_ae C hσ β] with ω hω
    intro a b
    dsimp [S, T]
    split_ifs
    · exact tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hω a.1) b.1
    · exact tendsto_const_nhds
  · intro n t
    change charFun ((multivariateGaussian 0 (fun a b : Fin N × Fin (n + 1) ↦
        if a.2 = b.2 then C a.1 b.1 else 0)).prod
        (initialization 1 (widths (n + 1) q Fin.elim0)) |>.map
          (upperLayer (n + 1) q σ β)) t = _
    rw [charFun_map_prod_of_conditional_law _ _ _
      (continuous_upperLayer (n + 1) q hc β).measurable
      (fun z ↦ multivariateGaussian 0 (upperLayerCovariance (n + 1) q σ β z))
      (fun z ↦ map_upperLayer_section (n + 1) q σ β z)]
    have hm : Continuous (fun z : EuclideanSpace ℝ (Fin N × Fin (n + 1)) ↦
        charFun (multivariateGaussian 0 (upperLayerCovariance (n + 1) q σ β z)) t) := by
      have he (a b : Fin N × Fin q) : Continuous (fun z ↦
          upperLayerCovariance (n + 1) q σ β z a b) := by
        unfold upperLayerCovariance
        split_ifs <;> fun_prop
      simp_rw [charFun_multivariateGaussian (upperLayerCovariance_posSemidef _ _ _ _ _)]
      simp only [Matrix.mulVec, dotProduct]
      fun_prop
    rw [← (measurePreserving_gaussianPrefix C hC (n + 1)).map_eq,
      integral_map (measurePreserving_gaussianPrefix C hC (n + 1)).measurable.aemeasurable
        hm.aestronglyMeasurable]
    simp_rw [upperLayerCovariance_gaussianPrefix]
    rfl

theorem gaussianUpperLaw_covarianceKernel_tendsto {N : ℕ} (d q h : ℕ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (β : ℝ)
    (X : Fin N → Input d) :
    Tendsto (β := ProbabilityMeasure (EuclideanSpace ℝ (Fin N × Fin q)))
      (fun n ↦ gaussianUpperLaw
        (fun i j ↦ covarianceKernel d σ β h (X i) (X j)) (n + 1) q σ hσ.continuous β)
      atTop (𝓝 ⟨outputGaussian d q σ β (h + 1) X, inferInstance⟩) := by
  have hC := covarianceKernel_posSemidef d hσ β h N X
  simpa only [outputGaussian, covarianceKernel,
    gaussianProductExpectation_eq_integral_family X hC hσ] using
    gaussianUpperLaw_tendsto (fun i j ↦ covarianceKernel d σ β h (X i) (X j)) hC q hσ β

def lastWidthEquality {h : ℕ} (d q : ℕ) (w : Fin h → ℕ) (n : ℕ) :
    ∀ l, l ≤ 1 → affineLayerWidth (h + 1) (widths d q (Fin.snoc w n)) l =
      widths (n + 1) q Fin.elim0 l := by
  intro l hl
  interval_cases l
  · simp only [affineLayerWidth, widths]
    simpa only [widths, Nat.add_one_ne_zero, if_false, Nat.add_sub_cancel,
      Nat.lt_irrefl, dite_false] using widths_snoc_le d q w n (h + 1) le_rfl
  · simp [affineLayerWidth, widths]

def splitWidthParameters {h : ℕ} (d q : ℕ) (w : Fin h → ℕ) (n : ℕ) :
    Parameters (h + 2) (widths d q (Fin.snoc w n)) ≃ᵐ
      (Parameters (h + 1) (widths d (n + 1) w) ×
        Parameters 1 (widths (n + 1) q Fin.elim0)) :=
  (splitParameters (h + 1) (widths d q (Fin.snoc w n))).trans
    (MeasurableEquiv.prodCongr
      (transportParameters (fun l hl ↦ widths_snoc_le d q w n l hl))
      (transportParameters (lastWidthEquality d q w n)))

theorem measurePreserving_splitWidthParameters {h : ℕ}
    (d q : ℕ) (w : Fin h → ℕ) (n : ℕ) :
    MeasurePreserving (splitWidthParameters d q w n)
      (initialization (h + 2) (widths d q (Fin.snoc w n)))
      ((initialization (h + 1) (widths d (n + 1) w)).prod
        (initialization 1 (widths (n + 1) q Fin.elim0))) :=
  ((measurePreserving_transportParameters (fun l hl ↦ widths_snoc_le d q w n l hl)).prod
    (measurePreserving_transportParameters (lastWidthEquality d q w n))).comp
      (measurePreserving_splitParameters (h + 1) (widths d q (Fin.snoc w n)))

theorem initializedOutput_snoc_split {h N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) (w : Fin h → ℕ) (n : ℕ)
    (θ : Parameters (h + 2) (widths d q (Fin.snoc w n))) :
    initializedOutput d q σ β X (Fin.snoc w n) θ =
      upperLayer (n + 1) q σ β
        (initializedOutput d (n + 1) σ β X w (splitWidthParameters d q w n θ).1,
          (splitWidthParameters d q w n θ).2) := by
  let v := widths d q (Fin.snoc w n)
  let θs := splitParameters (h + 1) v θ
  let hvw := fun l hl ↦ widths_snoc_le d q w n l hl
  ext a
  change network (h + 2) v σ β θ (inputForWidths d q (Fin.snoc w n) (X a.1))
      (outputForWidths d q (Fin.snoc w n) a.2) = _
  rw [network_split_last (h + 1) (Nat.zero_lt_succ h)]
  have hpre (i : Fin (n + 1)) :
      initializedOutput d (n + 1) σ β X w (transportParameters hvw θs.1) (a.1, i) =
        network (h + 1) v σ β θs.1 (inputForWidths d q (Fin.snoc w n) (X a.1))
          (Fin.cast (hvw (h + 1) le_rfl).symm (outputForWidths d (n + 1) w i)) := by
    exact network_transport_apply hvw σ β θs.1
      (inputForWidths d q (Fin.snoc w n) (X a.1)) (outputForWidths d (n + 1) w i)
  change _ = network 1 (widths (n + 1) q Fin.elim0) σ β
    (transportParameters (lastWidthEquality d q w n) θs.2)
    (inputForWidths (n + 1) q Fin.elim0 (fun i ↦ σ
      (initializedOutput d (n + 1) σ β X w (transportParameters hvw θs.1) (a.1, i))))
    (outputForWidths (n + 1) q Fin.elim0 a.2)
  simp_rw [hpre]
  have ht := network_transport_apply (lastWidthEquality d q w n) σ β θs.2
    (fun i ↦ σ (network (h + 1) v σ β θs.1
      (inputForWidths d q (Fin.snoc w n) (X a.1)) i))
    (outputForWidths (n + 1) q Fin.elim0 a.2)
  exact ht.symm

theorem initializedOutput_snoc_law {h N : ℕ} (d q : ℕ) {σ : ℝ → ℝ}
    {K : ℝ≥0} (hσ : LipschitzWith K σ) (β : ℝ) (X : Fin N → Input d)
    (w : Fin h → ℕ) (n : ℕ) :
    (initialization (h + 2) (widths d q (Fin.snoc w n))).map
        (initializedOutput d q σ β X (Fin.snoc w n)) =
      (((initialization (h + 1) (widths d (n + 1) w)).map
          (initializedOutput d (n + 1) σ β X w)).prod
        (initialization 1 (widths (n + 1) q Fin.elim0))).map
          (upperLayer (n + 1) q σ β) := by
  have hfun : initializedOutput d q σ β X (Fin.snoc w n) =
      (upperLayer (n + 1) q σ β ∘
        Prod.map (initializedOutput d (n + 1) σ β X w) id) ∘
          splitWidthParameters d q w n := funext (initializedOutput_snoc_split d q σ β X w n)
  have ho := (continuous_upperLayer (N := N) (n + 1) q hσ.continuous β).measurable
  have hi := measurable_initializedOutput d (n + 1) hσ β X w
  rw [hfun, ← Measure.map_map (ho.comp (hi.prodMap measurable_id))
    (splitWidthParameters d q w n).measurable,
    (measurePreserving_splitWidthParameters d q w n).map_eq,
    ← Measure.map_map ho (hi.prodMap measurable_id)]
  congr 1
  rw [← Measure.map_prod_map _ _ hi measurable_id, Measure.map_id]

def initializedLaw {h N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (β : ℝ) (X : Fin N → Input d) (w : Fin h → ℕ) :
    ProbabilityMeasure (EuclideanSpace ℝ (Fin N × Fin q)) :=
  ⟨(initialization (h + 1) (widths d q w)).map (initializedOutput d q σ β X w),
    Measure.isProbabilityMeasure_map (measurable_initializedOutput d q hσ β X w).aemeasurable⟩

theorem initializedLaw_snoc {h N : ℕ} (d q : ℕ) {σ : ℝ → ℝ}
    {K : ℝ≥0} (hσ : LipschitzWith K σ) (β : ℝ) (X : Fin N → Input d)
    (w : Fin h → ℕ) (n : ℕ) :
    initializedLaw d q σ hσ β X (Fin.snoc w n) =
      ProbabilityMeasure.map
        ((initializedLaw d (n + 1) σ hσ β X w).prod
          (⟨initialization 1 (widths (n + 1) q Fin.elim0), inferInstance⟩ :
            ProbabilityMeasure (Parameters 1 (widths (n + 1) q Fin.elim0))))
        (continuous_upperLayer (n + 1) q hσ.continuous β).measurable.aemeasurable := by
  apply Subtype.ext
  exact initializedOutput_snoc_law d q hσ β X w n

theorem gaussianInitialization_all {N : ℕ} (d q : ℕ) {σ : ℝ → ℝ}
    {K : ℝ≥0} (hσ : LipschitzWith K σ) (β : ℝ) (h : ℕ) (X : Fin N → Input d) :
    TendstoInDistribution (initializedOutput (h := h) d q σ β X)
      (sequentialWidths h) id (fun w ↦ initialization (h + 1) (widths d q w))
      (outputGaussian d q σ β h X) := by
  induction h generalizing q with
  | zero => exact gaussianInitialization_zero d q hσ β X
  | succ h ih =>
      refine ⟨fun w ↦ (measurable_initializedOutput d q hσ β X w).aemeasurable,
        aemeasurable_id, ?_⟩
      simp only [Measure.map_id]
      change Tendsto (initializedLaw d q σ hσ β X) (sequentialWidths (h + 1))
        (𝓝 (⟨outputGaussian d q σ β (h + 1) X, inferInstance⟩ :
          ProbabilityMeasure (EuclideanSpace ℝ (Fin N × Fin q))))
      apply tendsto_sequentialWidths_succ (g := fun n ↦ gaussianUpperLaw
        (fun i j ↦ covarianceKernel d σ β h (X i) (X j)) (n + 1) q σ hσ.continuous β)
      · intro n
        let ρ : ProbabilityMeasure (Parameters 1 (widths (n + 1) q Fin.elim0)) :=
          ⟨initialization 1 (widths (n + 1) q Fin.elim0), inferInstance⟩
        let ν : ProbabilityMeasure (EuclideanSpace ℝ (Fin N × Fin (n + 1))) :=
          ⟨outputGaussian d (n + 1) σ β h X, inferInstance⟩
        have hi : Tendsto (initializedLaw d (n + 1) σ hσ β X)
            (sequentialWidths h) (𝓝 ν) := by
          simpa only [Measure.map_id] using (ih (n + 1)).tendsto
        have hp : Tendsto (fun w ↦ (initializedLaw d (n + 1) σ hσ β X w).prod ρ)
            (sequentialWidths h) (𝓝 (ν.prod ρ)) := by
          have hpair : Tendsto (fun w ↦ (initializedLaw d (n + 1) σ hσ β X w, ρ))
              (sequentialWidths h) (𝓝 (ν, ρ)) := hi.prodMk_nhds tendsto_const_nhds
          exact (ProbabilityMeasure.continuous_prod.tendsto (ν, ρ)).comp hpair
        have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hp
          (continuous_upperLayer (n + 1) q hσ.continuous β)
        simpa only [initializedLaw_snoc] using hm
      · exact gaussianUpperLaw_covarianceKernel_tendsto d q h hσ β X

end JGH

end

/- Bundled from Definitions/JGH/Activation.lean. -/
/-!
Local proof infrastructure for the nonsmooth activation convention in JGH, Section 4.1,
PDF p. 5, Remark 3, and Appendix A.1, PDF pp. 12–13. These facts do not establish
the width limit or assert that a Lipschitz activation has an almost-everywhere continuous derivative.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace JGH

/-- Scalar Gaussian density domination, independent of its mean. -/
theorem gaussianReal_le_density_bound (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    gaussianReal m v ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * v))⁻¹) • (volume : Measure ℝ) := by
  rw [gaussianReal_of_var_ne_zero m hv, ← withDensity_const]
  apply withDensity_mono
  filter_upwards [] with t
  apply ENNReal.ofReal_le_ofReal
  unfold gaussianPDFReal
  apply mul_le_of_le_one_right (by positivity)
  apply Real.exp_le_one_iff.mpr
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) (by positivity)

theorem activation_differentiable_gaussian_ae {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    ∀ᵐ t ∂gaussianReal m v, DifferentiableAt ℝ σ t :=
  (gaussianReal_absolutelyContinuous m hv).ae_le hσ.ae_differentiableAt_real

theorem activation_derivative_measurable (σ : ℝ → ℝ) : Measurable (deriv σ) :=
  measurable_deriv σ

theorem activation_derivative_bound {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (t : ℝ) : ‖deriv σ t‖ ≤ K :=
  norm_deriv_le_of_lipschitz hσ

theorem activation_derivative_memLp {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (μ : Measure ℝ) [IsFiniteMeasure μ] (p : ℝ≥0∞) :
    MemLp (deriv σ) p μ :=
  MemLp.of_bound (aestronglyMeasurable_deriv σ μ) K
    (Filter.Eventually.of_forall (activation_derivative_bound hσ))

theorem gaussianPair_derivative_memLp {d : ℕ} (C : Kernel d)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (x y : Input d)
    (i : Fin 2) (p : ℝ≥0∞) :
    MemLp (fun z : EuclideanSpace ℝ (Fin 2) ↦ deriv σ (z i)) p (gaussianPair C x y) := by
  haveI : IsProbabilityMeasure (gaussianPair C x y) := by
    unfold gaussianPair
    infer_instance
  exact MemLp.of_bound ((measurable_deriv σ).comp (by fun_prop)).aestronglyMeasurable K
    (Filter.Eventually.of_forall (fun _ ↦ activation_derivative_bound hσ _))

theorem gaussianPair_activation_differentiable_ae {d : ℕ} (C : Kernel d)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (x y : Input d)
    (hC : (Matrix.of (fun i j : Fin 2 ↦ C (![x, y] i) (![x, y] j))).PosSemidef)
    (i : Fin 2) (hv : 0 < C (![x, y] i) (![x, y] i)) :
    ∀ᵐ z ∂gaussianPair C x y, DifferentiableAt ℝ σ (z i) := by
  exact (measurePreserving_eval_multivariateGaussian (μ := 0) hC).quasiMeasurePreserving.ae
    (activation_differentiable_gaussian_ae hσ _ (Real.toNNReal_pos.mpr hv).ne')

theorem parameterDerivative_measurable (L : ℕ) (width : ℕ → ℕ) (σ : ℝ → ℝ)
    (β : ℝ) (x : Fin (width 0) → ℝ) (k : Fin (width L))
    (p : ParameterIndex L width) :
    Measurable (fun θ ↦ parameterDerivative L width σ β θ x k p) := by
  classical
  exact measurable_fderiv_apply_const ℝ (fun θ ↦ network L width σ β θ x k)
    (Pi.single p 1)

theorem finiteNTK_measurable (L : ℕ) (width : ℕ → ℕ) (σ : ℝ → ℝ)
    (β : ℝ) (x y : Fin (width 0) → ℝ) (k k' : Fin (width L)) :
    Measurable (fun θ ↦ finiteNTK L width σ β θ x y k k') := by
  classical
  unfold finiteNTK
  exact Finset.measurable_sum _ fun p _ ↦
    (parameterDerivative_measurable L width σ β x k p).mul
      (parameterDerivative_measurable L width σ β y k' p)

theorem gaussianPair_derivative_product_integrable {d : ℕ} (C : Kernel d)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (x y : Input d) :
    Integrable (fun z : EuclideanSpace ℝ (Fin 2) ↦ deriv σ (z 0) * deriv σ (z 1))
      (gaussianPair C x y) := by
  haveI : IsProbabilityMeasure (gaussianPair C x y) := by
    unfold gaussianPair
    infer_instance
  apply Integrable.of_bound (by fun_prop) ((K : ℝ) ^ 2)
  filter_upwards [] with z
  rw [norm_mul, pow_two]
  exact mul_le_mul (norm_deriv_le_of_lipschitz hσ)
    (norm_deriv_le_of_lipschitz hσ) (norm_nonneg _) K.coe_nonneg

theorem gaussianProductExpectation_derivative_bound {d : ℕ} (C : Kernel d)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (x y : Input d) :
    ‖gaussianProductExpectation C (deriv σ) x y‖ ≤ (K : ℝ) ^ 2 := by
  haveI : IsProbabilityMeasure (gaussianPair C x y) := by
    unfold gaussianPair
    infer_instance
  have hbound : ∀ᵐ z ∂gaussianPair C x y,
      ‖deriv σ (z 0) * deriv σ (z 1)‖ ≤ (K : ℝ) ^ 2 := by
    filter_upwards [] with z
    rw [norm_mul, pow_two]
    exact mul_le_mul (norm_deriv_le_of_lipschitz hσ)
      (norm_deriv_le_of_lipschitz hσ) (norm_nonneg _) K.coe_nonneg
  simpa [gaussianProductExpectation] using norm_integral_le_of_norm_le_const hbound

end JGH

end

/- Bundled from Definitions/JGH/NTKOuterLimit.lean. -/
/-!
The outer-width law of large numbers in Jacot--Gabriel--Hongler,
arXiv:1806.07572v4, Appendix A.1, Theorem 1 proof, PDF p. 13.
Each iid sample consists of a Gaussian preactivation vector and an independent
standard Gaussian vector of final-layer output weights.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology ENNReal NNReal
namespace JGH

lemma gaussianProductExpectation_eq_integral_family_measurable {d N : ℕ} {C : Kernel d}
    (X : Fin N → Input d)
    (hC : (Matrix.of (fun i j ↦ C (X i) (X j))).PosSemidef)
    {φ : ℝ → ℝ} (hφ : Measurable φ) (i j : Fin N) :
    gaussianProductExpectation C φ (X i) (X j) =
      ∫ z : EuclideanSpace ℝ (Fin N), φ (z i) * φ (z j)
        ∂multivariateGaussian 0 (Matrix.of (fun a b ↦ C (X a) (X b))) := by
  have hm : Measure.map (coordinateMap ![i, j])
      (multivariateGaussian 0 (Matrix.of (fun a b ↦ C (X a) (X b)))) =
        gaussianPair C (X i) (X j) := by
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

lemma gaussian_derivative_product_integrable {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι ℝ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (i j : ι) :
    Integrable (fun z : EuclideanSpace ℝ ι ↦ deriv σ (z i) * deriv σ (z j))
      (multivariateGaussian 0 C) := by
  have hmem (i : ι) : MemLp (fun z : EuclideanSpace ℝ ι ↦ deriv σ (z i)) 2
      (multivariateGaussian 0 C) :=
    MemLp.of_bound ((measurable_deriv σ).comp (by fun_prop)).aestronglyMeasurable K
      (Eventually.of_forall fun _ ↦ activation_derivative_bound hσ _)
  exact (hmem i).integrable_mul (hmem j)

lemma gaussian_standard_weight_product {κ : Type*} [Fintype κ] [DecidableEq κ]
    (k k' : κ) :
    (∫ z : EuclideanSpace ℝ κ, z k * z k'
      ∂multivariateGaussian 0 (1 : Matrix κ κ ℝ)) = if k = k' then 1 else 0 := by
  have hmem (k : κ) : MemLp (fun z : EuclideanSpace ℝ κ ↦ z k) 2
      (multivariateGaussian 0 (1 : Matrix κ κ ℝ)) := by
    simpa using activation_memLp_two 0 (1 : Matrix κ κ ℝ) LipschitzWith.id k
  have hm (k : κ) : (∫ z : EuclideanSpace ℝ κ, z k
      ∂multivariateGaussian 0 (1 : Matrix κ κ ℝ)) = 0 := by
    have h := (EuclideanSpace.proj (𝕜 := ℝ) k).integral_comp_id_comm
      (μ := multivariateGaussian 0 (1 : Matrix κ κ ℝ)) IsGaussian.integrable_id
    simpa using h
  have h := covariance_eval_multivariateGaussian (μ := (0 : EuclideanSpace ℝ κ))
    (Matrix.PosSemidef.one : (1 : Matrix κ κ ℝ).PosSemidef) k k'
  rw [covariance_eq_sub (hmem k) (hmem k'), hm, hm, mul_zero, sub_zero] at h
  simpa only [Matrix.one_apply] using h

def ntkNeuronLaw {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C : Matrix ι ι ℝ) : Measure (EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) :=
  (multivariateGaussian 0 C).prod (multivariateGaussian 0 (1 : Matrix κ κ ℝ))

instance {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C : Matrix ι ι ℝ) : IsProbabilityMeasure (ntkNeuronLaw (κ := κ) C) := by
  unfold ntkNeuronLaw
  infer_instance

def derivativeNeuronFeature {ι κ : Type*} (σ : ℝ → ℝ) (i j : ι) (k k' : κ)
    (z : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ) : ℝ :=
  (deriv σ (z.1 i) * deriv σ (z.1 j)) * (z.2 k * z.2 k')

lemma derivativeNeuronFeature_integrable {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (C : Matrix ι ι ℝ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (i j : ι) (k k' : κ) :
    Integrable (derivativeNeuronFeature σ i j k k') (ntkNeuronLaw C) := by
  have hmem (k : κ) : MemLp (fun z : EuclideanSpace ℝ κ ↦ z k) 2
      (multivariateGaussian 0 (1 : Matrix κ κ ℝ)) := by
    simpa using activation_memLp_two 0 (1 : Matrix κ κ ℝ) LipschitzWith.id k
  exact (gaussian_derivative_product_integrable C hσ i j).mul_prod
    ((hmem k).integrable_mul (hmem k'))

lemma integral_derivativeNeuronFeature {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (C : Matrix ι ι ℝ)
    (σ : ℝ → ℝ) (i j : ι) (k k' : κ) :
    (∫ z, derivativeNeuronFeature σ i j k k' z ∂ntkNeuronLaw C) =
      if k = k' then (∫ u : EuclideanSpace ℝ ι, deriv σ (u i) * deriv σ (u j)
        ∂multivariateGaussian 0 C) else 0 := by
  unfold ntkNeuronLaw derivativeNeuronFeature
  rw [integral_prod_mul (fun u : EuclideanSpace ℝ ι ↦ deriv σ (u i) * deriv σ (u j))
    (fun w : EuclideanSpace ℝ κ ↦ w k * w k'), gaussian_standard_weight_product]
  split_ifs <;> simp

lemma derivativeNeuronFeature_tendsto_ae {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (C : Matrix ι ι ℝ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (i j : ι) (k k' : κ) :
    ∀ᵐ ω : ℕ → EuclideanSpace ℝ ι × EuclideanSpace ℝ κ
        ∂Measure.infinitePi (fun _ : ℕ ↦ ntkNeuronLaw C),
      Tendsto (fun n : ℕ ↦ (∑ a ∈ Finset.range (n + 1),
        derivativeNeuronFeature σ i j k k' (ω a)) / (n + 1 : ℕ)) atTop
        (𝓝 (if k = k' then (∫ u : EuclideanSpace ℝ ι,
          deriv σ (u i) * deriv σ (u j) ∂multivariateGaussian 0 C) else 0)) := by
  have h := iid_empirical_mean_tendsto_ae (ntkNeuronLaw C)
    (f := derivativeNeuronFeature σ i j k k')
    (by
      have hd : Measurable (deriv σ) := measurable_deriv σ
      unfold derivativeNeuronFeature
      fun_prop)
    (derivativeNeuronFeature_integrable C hσ i j k k')
  rw [integral_derivativeNeuronFeature] at h
  filter_upwards [h] with ω hω
  exact hω.comp (tendsto_add_atTop_nat 1)

lemma activationNeuronFeature_tendsto_ae {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (C : Matrix ι ι ℝ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (i j : ι) :
    ∀ᵐ ω : ℕ → EuclideanSpace ℝ ι × EuclideanSpace ℝ κ
        ∂Measure.infinitePi (fun _ : ℕ ↦ ntkNeuronLaw C),
      Tendsto (fun n : ℕ ↦ (∑ a ∈ Finset.range (n + 1),
        σ ((ω a).1 i) * σ ((ω a).1 j)) / (n + 1 : ℕ)) atTop
        (𝓝 (∫ u : EuclideanSpace ℝ ι, σ (u i) * σ (u j) ∂multivariateGaussian 0 C)) := by
  have hc : Continuous σ := hσ.continuous
  have hint : Integrable
      (fun z : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ ↦ σ (z.1 i) * σ (z.1 j))
      (ntkNeuronLaw C) := by
    simpa only [mul_one, ntkNeuronLaw] using ((activation_memLp_two 0 C hσ i).integrable_mul
      (activation_memLp_two 0 C hσ j)).mul_prod
        (integrable_const (μ := multivariateGaussian 0 (1 : Matrix κ κ ℝ)) (1 : ℝ))
  have he : (∫ z : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ,
      σ (z.1 i) * σ (z.1 j) ∂ntkNeuronLaw C) =
        ∫ u : EuclideanSpace ℝ ι, σ (u i) * σ (u j) ∂multivariateGaussian 0 C := by
    rw [ntkNeuronLaw, integral_fun_fst (fun u : EuclideanSpace ℝ ι ↦ σ (u i) * σ (u j))]
    simp
  have h := iid_empirical_mean_tendsto_ae (ntkNeuronLaw (κ := κ) C)
    (f := fun z ↦ σ (z.1 i) * σ (z.1 j)) (by fun_prop) hint
  rw [he] at h
  filter_upwards [h] with ω hω
  exact hω.comp (tendsto_add_atTop_nat 1)

def empiricalOuterNTK {N q : ℕ} (d : ℕ) (σ : ℝ → ℝ) (β : ℝ) (h : ℕ)
    (X : Fin N → Input d) (n : ℕ)
    (ω : ℕ → EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin q)) :
    Matrix (Fin N × Fin q) (Fin N × Fin q) ℝ := fun a b ↦
  limitingNTK d σ β h (X a.1) (X b.1) *
    ((∑ r ∈ Finset.range (n + 1), derivativeNeuronFeature σ a.1 b.1 a.2 b.2 (ω r)) /
      (n + 1 : ℕ)) +
    if a.2 = b.2 then (∑ r ∈ Finset.range (n + 1), σ ((ω r).1 a.1) * σ ((ω r).1 b.1)) /
      (n + 1 : ℕ) + β ^ 2 else 0

lemma empiricalOuterNTK_tendsto_ae {N q : ℕ} (d : ℕ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (β : ℝ) (h : ℕ) (X : Fin N → Input d) :
    ∀ᵐ ω : ℕ → EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin q)
        ∂Measure.infinitePi (fun _ : ℕ ↦ ntkNeuronLaw
          (Matrix.of (fun i j ↦ covarianceKernel d σ β h (X i) (X j)))),
      Tendsto (fun n ↦ empiricalOuterNTK d σ β h X n ω) atTop
        (𝓝 (fun a b : Fin N × Fin q ↦
          if a.2 = b.2 then limitingNTK d σ β (h + 1) (X a.1) (X b.1) else 0)) := by
  let C : Matrix (Fin N) (Fin N) ℝ := fun i j ↦ covarianceKernel d σ β h (X i) (X j)
  have hd := fun (i j : Fin N) (k k' : Fin q) ↦
    derivativeNeuronFeature_tendsto_ae C hσ i j k k'
  have ha := fun (i j : Fin N) ↦ activationNeuronFeature_tendsto_ae (κ := Fin q) C hσ i j
  have hda := ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦
    ae_all_iff.mpr fun k ↦ ae_all_iff.mpr fun k' ↦ hd i j k k'
  have haa := ae_all_iff.mpr fun i ↦ ae_all_iff.mpr fun j ↦ ha i j
  filter_upwards [hda, haa] with ω hdω haω
  apply tendsto_pi_nhds.mpr
  intro a
  apply tendsto_pi_nhds.mpr
  intro b
  have hC := covarianceKernel_posSemidef d hσ β h N X
  have heD := gaussianProductExpectation_eq_integral_family_measurable X hC
    (measurable_deriv σ) a.1 b.1
  have heA := gaussianProductExpectation_eq_integral_family X hC hσ a.1 b.1
  by_cases hab : a.2 = b.2
  · have hd' := (hdω a.1 b.1 a.2 b.2).const_mul (limitingNTK d σ β h (X a.1) (X b.1))
    have ha' := (haω a.1 b.1).add_const (β ^ 2)
    simpa only [empiricalOuterNTK, hab, if_true, limitingNTK, covarianceKernel,
      heD, heA] using hd'.add ha'
  · have hd' := (hdω a.1 b.1 a.2 b.2).const_mul (limitingNTK d σ β h (X a.1) (X b.1))
    simpa only [empiricalOuterNTK, hab, if_false, mul_zero, add_zero] using hd'

abbrev NTKEntryIndex (N q : ℕ) := (Fin N × Fin q) × (Fin N × Fin q)

def outerNTKVector {N q : ℕ} (d : ℕ) (σ : ℝ → ℝ) (β : ℝ) (h : ℕ)
    (X : Fin N → Input d) (n : ℕ)
    (ω : ℕ → EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin q)) :
    EuclideanSpace ℝ (NTKEntryIndex N q) :=
  WithLp.toLp 2 (fun ab ↦ empiricalOuterNTK d σ β h X n ω ab.1 ab.2)

def deterministicNTKVector {N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ) (h : ℕ)
    (X : Fin N → Input d) : EuclideanSpace ℝ (NTKEntryIndex N q) :=
  WithLp.toLp 2 (fun ab ↦ if ab.1.2 = ab.2.2 then
    limitingNTK d σ β h (X ab.1.1) (X ab.2.1) else 0)

lemma measurable_outerNTKVector {N q : ℕ} (d : ℕ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (β : ℝ) (h : ℕ) (X : Fin N → Input d) (n : ℕ) :
    Measurable (outerNTKVector (q := q) d σ β h X n) := by
  have hc : Continuous σ := hσ.continuous
  have hd : Measurable (deriv σ) := measurable_deriv σ
  unfold outerNTKVector
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro ab
  unfold empiricalOuterNTK derivativeNeuronFeature
  split_ifs <;> fun_prop

lemma outerNTKVector_tendsto_ae {N q : ℕ} (d : ℕ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (β : ℝ) (h : ℕ) (X : Fin N → Input d) :
    ∀ᵐ ω : ℕ → EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin q)
        ∂Measure.infinitePi (fun _ : ℕ ↦ ntkNeuronLaw
          (Matrix.of (fun i j ↦ covarianceKernel d σ β h (X i) (X j)))),
      Tendsto (fun n ↦ outerNTKVector d σ β h X n ω) atTop
        (𝓝 (deterministicNTKVector d q σ β (h + 1) X)) := by
  have hc : Continuous (fun A : Matrix (Fin N × Fin q) (Fin N × Fin q) ℝ ↦
      WithLp.toLp 2 (fun ab : NTKEntryIndex N q ↦ A ab.1 ab.2)) := by fun_prop
  filter_upwards [empiricalOuterNTK_tendsto_ae (q := q) d hσ β h X] with ω hω
  exact hc.continuousAt.tendsto.comp hω

lemma outerNTKVector_tendstoInDistribution {N q : ℕ} (d : ℕ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (β : ℝ) (h : ℕ) (X : Fin N → Input d) :
    TendstoInDistribution (outerNTKVector (q := q) d σ β h X) atTop id
      (fun _ ↦ Measure.infinitePi (fun _ : ℕ ↦ ntkNeuronLaw
        (Matrix.of (fun i j ↦ covarianceKernel d σ β h (X i) (X j)))))
      (Measure.dirac (deterministicNTKVector d q σ β (h + 1) X)) := by
  have hm := tendstoInMeasure_of_tendsto_ae
    (fun n ↦ (measurable_outerNTKVector (q := q) d hσ β h X n).aestronglyMeasurable)
    (outerNTKVector_tendsto_ae (q := q) d hσ β h X)
  have hd := hm.tendstoInDistribution
    (fun n ↦ (measurable_outerNTKVector (q := q) d hσ β h X n).aemeasurable)
  refine ⟨fun n ↦ (measurable_outerNTKVector (q := q) d hσ β h X n).aemeasurable,
    measurable_id.aemeasurable, ?_⟩
  simpa only [Measure.map_const, measure_univ, one_smul, Measure.map_id] using hd.tendsto

end JGH

end

/- Bundled from Definitions/JGH/NTKRecursion.lean. -/
/-!
The parameter chain rule for Jacot--Gabriel--Hongler, arXiv:1806.07572v4,
Appendix A.1, Theorem 1 proof, PDF p. 13 (unnumbered displays).
Pointwise differentiability hypotheses here are intermediate hypotheses, not changes to the mission.
-/

noncomputable section

open scoped BigOperators

namespace JGH

def prefixParametersLinear (L : ℕ) (width : ℕ → ℕ) :
    Parameters (L + 1) width →L[ℝ] Parameters L width where
  toFun θ p := θ (parameterIndexSplit L width (Sum.inl p))
  map_add' θ η := by ext p; rfl
  map_smul' c θ := by ext p; rfl

def lastParametersLinear (L : ℕ) (width : ℕ → ℕ) :
    Parameters (L + 1) width →L[ℝ] Parameters 1 (affineLayerWidth L width) where
  toFun θ p := θ (parameterIndexSplit L width (Sum.inr p))
  map_add' θ η := by ext p; rfl
  map_smul' c θ := by ext p; rfl

lemma prefixParametersLinear_eq_split (L : ℕ) (width : ℕ → ℕ)
    (θ : Parameters (L + 1) width) :
    prefixParametersLinear L width θ = (splitParameters L width θ).1 := by
  ext ⟨l, a⟩
  simp [prefixParametersLinear, parameterIndexSplit]

lemma lastParametersLinear_eq_split (L : ℕ) (width : ℕ → ℕ)
    (θ : Parameters (L + 1) width) :
    lastParametersLinear L width θ = (splitParameters L width θ).2 := by
  ext ⟨l, a⟩
  have hl : l = 0 := Subsingleton.elim _ _
  subst l
  simp [lastParametersLinear, parameterIndexSplit]

def splitParametersLinear (L : ℕ) (width : ℕ → ℕ) :
    Parameters (L + 1) width →L[ℝ]
      (Parameters L width × Parameters 1 (affineLayerWidth L width)) :=
  (prefixParametersLinear L width).prod (lastParametersLinear L width)

lemma splitParametersLinear_eq (L : ℕ) (width : ℕ → ℕ)
    (θ : Parameters (L + 1) width) :
    splitParametersLinear L width θ = splitParameters L width θ := by
  exact Prod.ext (prefixParametersLinear_eq_split L width θ)
    (lastParametersLinear_eq_split L width θ)

@[simp] lemma prefixParametersLinear_single_inl (L : ℕ) (width : ℕ → ℕ)
    (p : ParameterIndex L width) :
    prefixParametersLinear L width (Pi.single (parameterIndexSplit L width (Sum.inl p)) 1) =
      Pi.single p 1 := by
  classical
  ext q
  simp [prefixParametersLinear, Pi.single_apply]

@[simp] lemma prefixParametersLinear_single_inr (L : ℕ) (width : ℕ → ℕ)
    (p : ParameterIndex 1 (affineLayerWidth L width)) :
    prefixParametersLinear L width (Pi.single (parameterIndexSplit L width (Sum.inr p)) 1) =
      0 := by
  classical
  ext q
  simp [prefixParametersLinear]

@[simp] lemma lastParametersLinear_single_inl (L : ℕ) (width : ℕ → ℕ)
    (p : ParameterIndex L width) :
    lastParametersLinear L width (Pi.single (parameterIndexSplit L width (Sum.inl p)) 1) =
      0 := by
  classical
  ext q
  simp [lastParametersLinear]

@[simp] lemma lastParametersLinear_single_inr (L : ℕ) (width : ℕ → ℕ)
    (p : ParameterIndex 1 (affineLayerWidth L width)) :
    lastParametersLinear L width (Pi.single (parameterIndexSplit L width (Sum.inr p)) 1) =
      Pi.single p 1 := by
  classical
  ext q
  simp [lastParametersLinear, Pi.single_apply]

lemma network_succ_eq_prefix (L : ℕ) (hL : 0 < L) (width : ℕ → ℕ)
    (σ : ℝ → ℝ) (β : ℝ) (θ : Parameters (L + 1) width)
    (x : Fin (width 0) → ℝ) (k : Fin (width (L + 1))) :
    network (L + 1) width σ β θ x k =
      (Real.sqrt (width L))⁻¹ * ∑ i : Fin (width L),
        θ (parameterIndexSplit L width (Sum.inr ⟨0, k, some i⟩)) *
          σ (network L width σ β (prefixParametersLinear L width θ) x i) +
        β * θ (parameterIndexSplit L width (Sum.inr ⟨0, k, none⟩)) := by
  rw [network_split_last L hL]
  simp [network, preactivation, affineLayerWidth, prefixParametersLinear_eq_split,
    parameterIndexSplit, div_eq_inv_mul]
  simp [splitParameters, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft,
    Equiv.piCongrLeft', MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi,
    parameterIndexSplit]
  exact Or.inl rfl

def networkDerivativeRecursion (L : ℕ) (width : ℕ → ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters (L + 1) width) (x : Fin (width 0) → ℝ)
    (k : Fin (width (L + 1))) : Parameters (L + 1) width →L[ℝ] ℝ :=
  (Real.sqrt (width L))⁻¹ • ∑ i : Fin (width L),
    (θ (parameterIndexSplit L width (Sum.inr ⟨0, k, some i⟩)) •
      (deriv σ (network L width σ β (prefixParametersLinear L width θ) x i) •
        ((fderiv ℝ (fun η ↦ network L width σ β η x i)
          (prefixParametersLinear L width θ)).comp (prefixParametersLinear L width))) +
      σ (network L width σ β (prefixParametersLinear L width θ) x i) •
        ContinuousLinearMap.proj (parameterIndexSplit L width (Sum.inr ⟨0, k, some i⟩))) +
      β • ContinuousLinearMap.proj (parameterIndexSplit L width (Sum.inr ⟨0, k, none⟩))

lemma hasFDerivAt_network_succ (L : ℕ) (hL : 0 < L) (width : ℕ → ℕ)
    (σ : ℝ → ℝ) (β : ℝ) (θ : Parameters (L + 1) width)
    (x : Fin (width 0) → ℝ) (k : Fin (width (L + 1)))
    (hprefix : ∀ i, DifferentiableAt ℝ (fun η ↦ network L width σ β η x i)
      (prefixParametersLinear L width θ))
    (hσ : ∀ i, DifferentiableAt ℝ σ
      (network L width σ β (prefixParametersLinear L width θ) x i)) :
    HasFDerivAt (fun η ↦ network (L + 1) width σ β η x k)
      (networkDerivativeRecursion L width σ β θ x k) θ := by
  have hp (i : Fin (width L)) :=
    (hprefix i).hasFDerivAt.comp θ (prefixParametersLinear L width).hasFDerivAt
  have hs (i : Fin (width L)) := (hσ i).hasDerivAt.comp_hasFDerivAt θ (hp i)
  have hprod (i : Fin (width L)) :=
    (ContinuousLinearMap.proj
      (parameterIndexSplit L width (Sum.inr ⟨0, k, some i⟩))).hasFDerivAt.mul (hs i)
  have hsum := (HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hprod i)).const_mul
    (Real.sqrt (width L))⁻¹
  have hb := ((show Parameters (L + 1) width →L[ℝ] ℝ from ContinuousLinearMap.proj
    (parameterIndexSplit L width (Sum.inr ⟨0, k, none⟩))).hasFDerivAt (x := θ)).const_mul β
  simpa only [network_succ_eq_prefix L hL, networkDerivativeRecursion,
    Function.comp_apply, ContinuousLinearMap.proj_apply] using hsum.add hb

lemma parameterDerivative_succ_inl (L : ℕ) (hL : 0 < L) (width : ℕ → ℕ)
    (σ : ℝ → ℝ) (β : ℝ) (θ : Parameters (L + 1) width)
    (x : Fin (width 0) → ℝ) (k : Fin (width (L + 1)))
    (hprefix : ∀ i, DifferentiableAt ℝ (fun η ↦ network L width σ β η x i)
      (prefixParametersLinear L width θ))
    (hσ : ∀ i, DifferentiableAt ℝ σ
      (network L width σ β (prefixParametersLinear L width θ) x i))
    (p : ParameterIndex L width) :
    parameterDerivative (L + 1) width σ β θ x k
      (parameterIndexSplit L width (Sum.inl p)) =
      (Real.sqrt (width L))⁻¹ * ∑ i : Fin (width L),
        θ (parameterIndexSplit L width (Sum.inr ⟨0, k, some i⟩)) *
          deriv σ (network L width σ β (prefixParametersLinear L width θ) x i) *
          parameterDerivative L width σ β (prefixParametersLinear L width θ) x i p := by
  classical
  unfold parameterDerivative
  rw [(hasFDerivAt_network_succ L hL width σ β θ x k hprefix hσ).fderiv]
  simp [networkDerivativeRecursion, mul_assoc]

set_option backward.isDefEq.respectTransparency false in
lemma parameterDerivative_succ_inr (L : ℕ) (hL : 0 < L) (width : ℕ → ℕ)
    (σ : ℝ → ℝ) (β : ℝ) (θ : Parameters (L + 1) width)
    (x : Fin (width 0) → ℝ) (k : Fin (width (L + 1)))
    (hprefix : ∀ i, DifferentiableAt ℝ (fun η ↦ network L width σ β η x i)
      (prefixParametersLinear L width θ))
    (hσ : ∀ i, DifferentiableAt ℝ σ
      (network L width σ β (prefixParametersLinear L width θ) x i))
    (p : ParameterIndex 1 (affineLayerWidth L width)) :
    parameterDerivative (L + 1) width σ β θ x k
      (parameterIndexSplit L width (Sum.inr p)) =
      parameterDerivative 1 (affineLayerWidth L width) σ β
        (lastParametersLinear L width θ)
        (fun i ↦ σ (network L width σ β (prefixParametersLinear L width θ) x i)) k p := by
  classical
  unfold parameterDerivative
  rw [(hasFDerivAt_network_succ L hL width σ β θ x k hprefix hσ).fderiv]
  simp_rw [network_one_eq_linear]
  rw [ContinuousLinearMap.fderiv]
  simp [networkDerivativeRecursion, affineOutputLinear, Pi.single_apply, affineLayerWidth]
  simp [ContinuousLinearMap.proj, LinearMap.proj, Pi.single_apply]

lemma sum_mul_sum_gram {P I J : Type*} [Fintype P] [Fintype I] [Fintype J]
    (A : I → ℝ) (B : J → ℝ) (F : I → P → ℝ) (G : J → P → ℝ) :
    (∑ p, (∑ i, A i * F i p) * (∑ j, B j * G j p)) =
      ∑ i, ∑ j, A i * B j * (∑ p, F i p * G j p) := by
  simp only [Finset.sum_mul]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro p _
  ring

lemma finiteNTK_succ_split (L : ℕ) (hL : 0 < L) (width : ℕ → ℕ)
    (σ : ℝ → ℝ) (β : ℝ) (θ : Parameters (L + 1) width)
    (x y : Fin (width 0) → ℝ) (k k' : Fin (width (L + 1)))
    (hpx : ∀ i, DifferentiableAt ℝ (fun η ↦ network L width σ β η x i)
      (prefixParametersLinear L width θ))
    (hpy : ∀ i, DifferentiableAt ℝ (fun η ↦ network L width σ β η y i)
      (prefixParametersLinear L width θ))
    (hsx : ∀ i, DifferentiableAt ℝ σ
      (network L width σ β (prefixParametersLinear L width θ) x i))
    (hsy : ∀ i, DifferentiableAt ℝ σ
      (network L width σ β (prefixParametersLinear L width θ) y i)) :
    finiteNTK (L + 1) width σ β θ x y k k' =
      (∑ p : ParameterIndex L width,
        parameterDerivative (L + 1) width σ β θ x k
          (parameterIndexSplit L width (Sum.inl p)) *
        parameterDerivative (L + 1) width σ β θ y k'
          (parameterIndexSplit L width (Sum.inl p))) +
      if k = k' then
        (∑ i : Fin (width L),
          σ (network L width σ β (prefixParametersLinear L width θ) x i) *
          σ (network L width σ β (prefixParametersLinear L width θ) y i)) / width L + β ^ 2
      else 0 := by
  classical
  unfold finiteNTK
  rw [← (parameterIndexSplit L width).sum_comp
    (fun p ↦ parameterDerivative (L + 1) width σ β θ x k p *
      parameterDerivative (L + 1) width σ β θ y k' p)]
  rw [Fintype.sum_sum_type]
  congr 1
  simp_rw [parameterDerivative_succ_inr L hL width σ β θ x k hpx hsx,
    parameterDerivative_succ_inr L hL width σ β θ y k' hpy hsy]
  exact finiteNTK_one (affineLayerWidth L width) σ β (lastParametersLinear L width θ)
    (fun i ↦ σ (network L width σ β (prefixParametersLinear L width θ) x i))
    (fun i ↦ σ (network L width σ β (prefixParametersLinear L width θ) y i)) k k'

lemma sum_scaled_mul_sum_gram {P I J : Type*} [Fintype P] [Fintype I] [Fintype J]
    (r : ℝ) (A : I → ℝ) (B : J → ℝ) (F : I → P → ℝ) (G : J → P → ℝ) :
    (∑ p, (r * ∑ i, A i * F i p) * (r * ∑ j, B j * G j p)) =
      r ^ 2 * ∑ i, ∑ j, A i * B j * (∑ p, F i p * G j p) := by
  have he (p : P) : (r * ∑ i, A i * F i p) * (r * ∑ j, B j * G j p) =
      r ^ 2 * ((∑ i, A i * F i p) * (∑ j, B j * G j p)) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, sum_mul_sum_gram]

/-- The full two-neuron contraction and the last-layer weight-and-bias contribution. -/
lemma finiteNTK_succ (L : ℕ) (hL : 0 < L) (width : ℕ → ℕ)
    (σ : ℝ → ℝ) (β : ℝ) (θ : Parameters (L + 1) width)
    (x y : Fin (width 0) → ℝ) (k k' : Fin (width (L + 1)))
    (hpx : ∀ i, DifferentiableAt ℝ (fun η ↦ network L width σ β η x i)
      (prefixParametersLinear L width θ))
    (hpy : ∀ i, DifferentiableAt ℝ (fun η ↦ network L width σ β η y i)
      (prefixParametersLinear L width θ))
    (hsx : ∀ i, DifferentiableAt ℝ σ
      (network L width σ β (prefixParametersLinear L width θ) x i))
    (hsy : ∀ i, DifferentiableAt ℝ σ
      (network L width σ β (prefixParametersLinear L width θ) y i)) :
    let η := prefixParametersLinear L width θ
    finiteNTK (L + 1) width σ β θ x y k k' =
      (∑ i : Fin (width L), ∑ j : Fin (width L),
        (θ (parameterIndexSplit L width (Sum.inr ⟨0, k, some i⟩)) *
          deriv σ (network L width σ β η x i)) *
        (θ (parameterIndexSplit L width (Sum.inr ⟨0, k', some j⟩)) *
          deriv σ (network L width σ β η y j)) * finiteNTK L width σ β η x y i j) /
        width L +
      if k = k' then
        (∑ i : Fin (width L), σ (network L width σ β η x i) *
          σ (network L width σ β η y i)) / width L + β ^ 2
      else 0 := by
  dsimp only
  rw [finiteNTK_succ_split L hL width σ β θ x y k k' hpx hpy hsx hsy]
  congr 1
  simp_rw [parameterDerivative_succ_inl L hL width σ β θ x k hpx hsx,
    parameterDerivative_succ_inl L hL width σ β θ y k' hpy hsy]
  have h := sum_scaled_mul_sum_gram (Real.sqrt (width L))⁻¹
    (fun i : Fin (width L) ↦ θ (parameterIndexSplit L width (Sum.inr ⟨0, k, some i⟩)) *
      deriv σ (network L width σ β (prefixParametersLinear L width θ) x i))
    (fun j : Fin (width L) ↦ θ (parameterIndexSplit L width (Sum.inr ⟨0, k', some j⟩)) *
      deriv σ (network L width σ β (prefixParametersLinear L width θ) y j))
    (fun i p ↦ parameterDerivative L width σ β (prefixParametersLinear L width θ) x i p)
    (fun j p ↦ parameterDerivative L width σ β (prefixParametersLinear L width θ) y j p)
  simpa only [finiteNTK, inv_pow, Real.sq_sqrt (Nat.cast_nonneg (width L)),
    div_eq_inv_mul] using h

end JGH

end

/- Bundled from Definitions/JGH/NetworkRegularity.lean. -/
/-!
Positive Gaussian bias removes the activation's null differentiability set.
This supplies the chain-rule hypotheses in Jacot--Gabriel--Hongler,
Appendix A.1, PDF pp. 12–13, without strengthening the Lipschitz assumption.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators NNReal ENNReal
namespace JGH

theorem map_affine_scalar (width : ℕ → ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (x : Fin (width 0) → ℝ) (k : Fin (width 1)) :
    (initialization 1 width).map (fun θ ↦ network 1 width σ β θ x k) =
      gaussianReal 0 (Real.toNNReal ((∑ i, x i * x i) / width 0 + β ^ 2)) := by
  let v : ℝ := (∑ i, x i * x i) / width 0 + β ^ 2
  let S : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ v
  have hS : S.PosSemidef := by
    simpa [S, v, covarianceKernel] using
      covarianceKernel_zero_posSemidef (width 0) 1 σ β (fun _ ↦ x)
  let F : Parameters 1 width → EuclideanSpace ℝ (Fin 1) :=
    fun θ ↦ WithLp.toLp 2 (fun _ ↦ network 1 width σ β θ x k)
  have hF : MeasurePreserving F (initialization 1 width) (multivariateGaussian 0 S) := by
    constructor
    · dsimp [F]
      simp_rw [network_one_eq_linear]
      fun_prop
    · simpa [F, S, v] using map_initialization_affine width σ β
        (fun _ : Fin 1 ↦ x) (fun _ ↦ k)
  exact ((measurePreserving_eval_multivariateGaussian (μ := 0) hS (i := 0)).comp hF).map_eq

theorem affine_scalar_density_bound (width : ℕ → ℕ) (σ : ℝ → ℝ) {β : ℝ}
    (hβ : 0 < β) (x : Fin (width 0) → ℝ) (k : Fin (width 1)) :
    (initialization 1 width).map (fun θ ↦ network 1 width σ β θ x k) ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * β ^ 2))⁻¹) • (volume : Measure ℝ) := by
  rw [map_affine_scalar]
  let v := (∑ i, x i * x i) / (width 0 : ℝ) + β ^ 2
  have hbase : β ^ 2 ≤ v := le_add_of_nonneg_left
    (div_nonneg (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (x i)) (Nat.cast_nonneg _))
  have hv : 0 < v := lt_of_lt_of_le (sq_pos_of_pos hβ) hbase
  refine (gaussianReal_le_density_bound 0 (Real.toNNReal_pos.mpr hv).ne').trans ?_
  have hc : ENNReal.ofReal ((Real.sqrt (2 * Real.pi * (Real.toNNReal v : ℝ)))⁻¹) ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * β ^ 2))⁻¹) := by
    apply ENNReal.ofReal_le_ofReal
    rw [Real.coe_toNNReal v hv.le]
    apply (inv_le_inv₀ (by positivity) (by positivity)).mpr
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hbase (by positivity))
  apply Measure.le_iff.mpr
  intro s _
  exact mul_le_mul_left hc (volume s)

theorem map_prod_le_of_conditional {Ω Λ E : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Λ] [MeasurableSpace E] (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure P] [SFinite Q] (F : Ω × Λ → E) (hF : Measurable F)
    (ν : Measure E) (hν : ∀ ω, Q.map (fun z ↦ F (ω, z)) ≤ ν) :
    (P.prod Q).map F ≤ ν := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply (hF hs)]
  calc
    _ ≤ ∫⁻ _ : Ω, ν s ∂P := by
      apply lintegral_mono
      intro ω
      have h := hν ω s
      have hω : Measurable (fun z ↦ F (ω, z)) :=
        hF.comp (measurable_const.prodMk measurable_id)
      simpa only [Measure.map_apply hω hs] using h
    _ = ν s := by simp

theorem activation_differentiable_affine_ae (width : ℕ → ℕ) {σ : ℝ → ℝ}
    {K : ℝ≥0} (hσ : LipschitzWith K σ) {β : ℝ} (hβ : 0 < β)
    (x : Fin (width 0) → ℝ) (k : Fin (width 1)) :
    ∀ᵐ θ ∂initialization 1 width, DifferentiableAt ℝ σ (network 1 width σ β θ x k) := by
  let v : ℝ := (∑ i, x i * x i) / width 0 + β ^ 2
  have hv : 0 < v := by
    dsimp [v]
    exact add_pos_of_nonneg_of_pos
      (div_nonneg (Finset.sum_nonneg fun i _ ↦ mul_self_nonneg (x i))
        (Nat.cast_nonneg _)) (sq_pos_of_pos hβ)
  let S : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ ↦ v
  have hS : S.PosSemidef := by
    simpa [S, v, covarianceKernel] using
      covarianceKernel_zero_posSemidef (width 0) 1 σ β (fun _ ↦ x)
  let F : Parameters 1 width → EuclideanSpace ℝ (Fin 1) :=
    fun θ ↦ WithLp.toLp 2 (fun _ ↦ network 1 width σ β θ x k)
  have hF : MeasurePreserving F (initialization 1 width) (multivariateGaussian 0 S) := by
    constructor
    · dsimp [F]
      simp_rw [network_one_eq_linear]
      fun_prop
    · simpa [F, S, v] using map_initialization_affine width σ β
        (fun _ : Fin 1 ↦ x) (fun _ ↦ k)
  have hE := (measurePreserving_eval_multivariateGaussian (μ := 0) hS (i := 0)).comp hF
  have hD := activation_differentiable_gaussian_ae hσ 0 (Real.toNNReal_pos.mpr hv).ne'
  exact hE.quasiMeasurePreserving.ae hD

theorem continuous_preactivation_joint (L : ℕ) (width : ℕ → ℕ)
    {σ : ℝ → ℝ} (hσ : Continuous σ) (β : ℝ) (l : ℕ) (j : Fin (width l)) :
    Continuous (fun t : Parameters L width × (Fin (width 0) → ℝ) ↦
      preactivation L width σ β t.1 t.2 l j) := by
  induction l with
  | zero => exact (continuous_apply j).comp continuous_snd
  | succ l ih =>
      simp only [preactivation]
      by_cases hl : l < L
      · simp only [dif_pos hl]
        apply Continuous.add
        · apply Continuous.div_const
          apply continuous_finsetSum
          intro i _
          apply Continuous.mul (by fun_prop)
          by_cases hz : l = 0
          · simp only [if_pos hz]
            exact ih i
          · simp only [if_neg hz]
            exact hσ.comp (ih i)
        · fun_prop
      · simp only [dif_neg hl]
        exact continuous_const

theorem network_succ_scalar_density_bound (L : ℕ) (hL : 0 < L) (width : ℕ → ℕ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) {β : ℝ} (hβ : 0 < β)
    (x : Fin (width 0) → ℝ) (k : Fin (width (L + 1))) :
    (initialization (L + 1) width).map (fun θ ↦ network (L + 1) width σ β θ x k) ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * β ^ 2))⁻¹) • (volume : Measure ℝ) := by
  let A := affineLayerWidth L width
  let F : Parameters L width × Parameters 1 A → ℝ := fun t ↦
    network 1 A σ β t.2 (fun i ↦ σ (network L width σ β t.1 x i)) k
  have hG : Continuous (fun t : Parameters L width × Parameters 1 A ↦
      fun i : Fin (width L) ↦ σ (network L width σ β t.1 x i)) := by
    apply continuous_pi
    intro i
    exact hσ.continuous.comp
      ((continuous_preactivation_parameters L width hσ.continuous β x L i).comp continuous_fst)
  have hF : Measurable F :=
    ((continuous_preactivation_joint 1 A hσ.continuous β 1 k).comp
      (continuous_snd.prodMk hG)).measurable
  have he : (fun θ ↦ network (L + 1) width σ β θ x k) = F ∘ splitParameters L width :=
    funext fun θ ↦ network_split_last L hL width σ β θ x k
  rw [he, ← Measure.map_map hF (splitParameters L width).measurable,
    (measurePreserving_splitParameters L width).map_eq]
  apply map_prod_le_of_conditional _ _ F hF
  intro η
  exact affine_scalar_density_bound A σ hβ (fun i ↦ σ (network L width σ β η x i)) k

theorem network_scalar_density_bound (L : ℕ) (hL : 0 < L) (width : ℕ → ℕ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) {β : ℝ} (hβ : 0 < β)
    (x : Fin (width 0) → ℝ) (k : Fin (width L)) :
    (initialization L width).map (fun θ ↦ network L width σ β θ x k) ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi * β ^ 2))⁻¹) • (volume : Measure ℝ) := by
  cases L with
  | zero => omega
  | succ L =>
      cases L with
      | zero => exact affine_scalar_density_bound width σ hβ x k
      | succ L =>
          exact network_succ_scalar_density_bound (L + 1) (Nat.succ_pos L) width hσ hβ x k

theorem activation_differentiable_network_ae (L : ℕ) (hL : 0 < L) (width : ℕ → ℕ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) {β : ℝ} (hβ : 0 < β)
    (x : Fin (width 0) → ℝ) (k : Fin (width L)) :
    ∀ᵐ θ ∂initialization L width, DifferentiableAt ℝ σ (network L width σ β θ x k) := by
  have hq : Measure.QuasiMeasurePreserving (fun θ ↦ network L width σ β θ x k)
      (initialization L width) (volume : Measure ℝ) :=
    ⟨(continuous_preactivation_parameters L width hσ.continuous β x L k).measurable,
      Measure.absolutelyContinuous_of_le_smul
        (network_scalar_density_bound L hL width hσ hβ x k)⟩
  exact hq.ae hσ.ae_differentiableAt_real

end JGH

end

/- Bundled from Definitions/JGH/NetworkDifferentiability.lean. -/
/-!
Almost-sure chain-rule hypotheses for the actual Gaussian-initialized network.
Source: Jacot--Gabriel--Hongler, Appendix A.1, PDF pp. 12–13, Theorem 1 proof.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
namespace JGH

theorem network_differentiable_parameters_ae (L : ℕ) (width : ℕ → ℕ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) {β : ℝ} (hβ : 0 < β)
    (x : Fin (width 0) → ℝ) (k : Fin (width L)) :
    ∀ᵐ θ ∂initialization L width,
      DifferentiableAt ℝ (fun η ↦ network L width σ β η x k) θ := by
  induction L with
  | zero =>
      exact Eventually.of_forall fun _ ↦ differentiableAt_const _
  | succ L ih =>
      by_cases hL : L = 0
      · subst L
        apply Eventually.of_forall
        intro θ
        change DifferentiableAt ℝ (fun η ↦ network 1 width σ β η x k) θ
        simp_rw [network_one_eq_linear]
        exact (affineOutputLinear width β x k).differentiableAt
      have hLp : 0 < L := Nat.pos_of_ne_zero hL
      have hmp : MeasurePreserving (fun θ ↦ (splitParameters L width θ).1)
          (initialization (L + 1) width) (initialization L width) :=
        measurePreserving_fst.comp (measurePreserving_splitParameters L width)
      have hp : ∀ᵐ θ ∂initialization (L + 1) width, ∀ i : Fin (width L),
          DifferentiableAt ℝ (fun η ↦ network L width σ β η x i)
            (prefixParametersLinear L width θ) := by
        apply ae_all_iff.mpr
        intro i
        simpa only [prefixParametersLinear_eq_split] using hmp.quasiMeasurePreserving.ae (ih i)
      have hs : ∀ᵐ θ ∂initialization (L + 1) width, ∀ i : Fin (width L),
          DifferentiableAt ℝ σ
            (network L width σ β (prefixParametersLinear L width θ) x i) := by
        apply ae_all_iff.mpr
        intro i
        simpa only [prefixParametersLinear_eq_split] using hmp.quasiMeasurePreserving.ae
          (activation_differentiable_network_ae L hLp width hσ hβ x i)
      filter_upwards [hp, hs] with θ hpθ hsθ
      exact (hasFDerivAt_network_succ L hLp width σ β θ x k hpθ hsθ).differentiableAt

/-- Simultaneous chain-rule hypotheses on every neuron of a fixed finite input family. -/
theorem network_succ_chain_hypotheses_ae {N : ℕ} (L : ℕ) (hL : 0 < L)
    (width : ℕ → ℕ) {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ)
    {β : ℝ} (hβ : 0 < β) (X : Fin N → Fin (width 0) → ℝ) :
    ∀ᵐ θ ∂initialization (L + 1) width, ∀ a : Fin N, ∀ i : Fin (width L),
      DifferentiableAt ℝ (fun η ↦ network L width σ β η (X a) i)
        (prefixParametersLinear L width θ) ∧
      DifferentiableAt ℝ σ
        (network L width σ β (prefixParametersLinear L width θ) (X a) i) := by
  have hmp : MeasurePreserving (fun θ ↦ (splitParameters L width θ).1)
      (initialization (L + 1) width) (initialization L width) :=
    measurePreserving_fst.comp (measurePreserving_splitParameters L width)
  apply ae_all_iff.mpr
  intro a
  apply ae_all_iff.mpr
  intro i
  have hp := hmp.quasiMeasurePreserving.ae
    (network_differentiable_parameters_ae L width hσ hβ (X a) i)
  have hs := hmp.quasiMeasurePreserving.ae
    (activation_differentiable_network_ae L hL width hσ hβ (X a) i)
  simpa only [prefixParametersLinear_eq_split] using hp.and hs

end JGH

end

/- Bundled from Definitions/JGH/MeasurableMapping.lean. -/
/-!
Law-level approximation for the measurable activation derivative in JGH,
Appendix A.1, PDF pp. 12–13. The scalar domination hypothesis is supplied by
the independent positive Gaussian bias; no continuity of the derivative is assumed.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal BoundedContinuousFunction

namespace JGH

def clipReal (B t : ℝ) : ℝ := min (max t (-B)) B

theorem clipReal_lipschitz (B : ℝ) : LipschitzWith 1 (clipReal B) :=
  (LipschitzWith.id.max_const (-B)).min_const B

theorem clipReal_norm_le {B : ℝ} (hB : 0 ≤ B) (t : ℝ) : ‖clipReal B t‖ ≤ B := by
  rw [Real.norm_eq_abs, abs_le]
  exact ⟨le_min (le_max_right _ _) (by linarith), min_le_right _ _⟩

theorem clipReal_eq_self {B t : ℝ} (ht : ‖t‖ ≤ B) : clipReal B t = t := by
  obtain ⟨hl, hu⟩ := abs_le.mp ht
  simp [clipReal, max_eq_left hl, min_eq_left hu]

theorem clipReal_error_le {B s t : ℝ} (hs : ‖s‖ ≤ B) :
    ‖s - clipReal B t‖ ≤ ‖s - t‖ := by
  simpa [Real.dist_eq, clipReal_eq_self hs] using (clipReal_lipschitz B).dist_le_mul s t

theorem exists_boundedContinuous_uniform_integral_approx_of_tight
    (S : Set (ProbabilityMeasure ℝ))
    (htight : IsTightMeasureSet ((fun μ : ProbabilityMeasure ℝ ↦ (μ : Measure ℝ)) '' S))
    (C : ℝ≥0) (hdom : ∀ μ ∈ S, (μ : Measure ℝ) ≤ C • (volume : Measure ℝ))
    {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t, ‖φ t‖ ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ →ᵇ ℝ, (∀ t, ‖g t‖ ≤ B) ∧
      ∀ μ ∈ S, (∫ t, ‖φ t - g t‖ ∂(μ : Measure ℝ)) < ε := by
  let δ := ε / (8 * (B + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨K, hK, htail⟩ :=
    isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
      (ENNReal.ofReal δ) (ENNReal.ofReal_pos.mpr hδ)
  let ν := volume.restrict K
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hφν : Integrable φ ν :=
    Integrable.of_bound hφ.aestronglyMeasurable B (Eventually.of_forall hbound)
  obtain ⟨g₀, hg₀, _⟩ := hφν.exists_boundedContinuous_integral_sub_le
    (show 0 < ε / (4 * ((C : ℝ) + 1)) by positivity)
  let g := g₀.comp (clipReal B) (clipReal_lipschitz B)
  have hgb (t : ℝ) : ‖g t‖ ≤ B := clipReal_norm_le hB _
  have herrν : Integrable (fun t ↦ ‖φ t - g t‖) ν :=
    (hφν.sub (g.integrable ν)).norm
  have hg : (∫ t, ‖φ t - g t‖ ∂ν) ≤ ε / (4 * ((C : ℝ) + 1)) := by
    refine (integral_mono herrν (hφν.sub (g₀.integrable ν)).norm ?_).trans hg₀
    intro t
    exact clipReal_error_le (hbound t)
  refine ⟨g, hgb, ?_⟩
  intro μ hμ
  have herr (t : ℝ) : ‖φ t - g t‖ ≤ 2 * B := by
    calc
      _ ≤ ‖φ t‖ + ‖g t‖ := norm_sub_le _ _
      _ ≤ 2 * B := by linarith [hbound t, hgb t]
  have hi : Integrable (fun t ↦ ‖φ t - g t‖) (μ : Measure ℝ) :=
    Integrable.of_bound ((hφ.sub g.continuous.measurable).norm.aestronglyMeasurable)
      (2 * B) (Eventually.of_forall (fun t ↦ by simpa using herr t))
  have hlocal : (∫ t in K, ‖φ t - g t‖ ∂(μ : Measure ℝ)) ≤
      (C : ℝ) * (ε / (4 * ((C : ℝ) + 1))) := by
    have hle : (μ : Measure ℝ).restrict K ≤ C • ν := by
      simpa only [ν, Measure.restrict_smul] using
        Measure.restrict_mono (s := K) (s' := K) Subset.rfl (hdom μ hμ)
    calc
      _ ≤ ∫ t, ‖φ t - g t‖ ∂(C • ν) :=
        integral_mono_measure hle (Eventually.of_forall (fun _ ↦ norm_nonneg _))
          (Integrable.of_bound (by fun_prop) (2 * B)
            (Eventually.of_forall (fun t ↦ by simpa using herr t)))
      _ = (C : ℝ) * (∫ t, ‖φ t - g t‖ ∂ν) := by
        rw [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hg C.coe_nonneg
  have htailμ : (μ : Measure ℝ).real Kᶜ ≤ δ := by
    have hle := htail (μ : Measure ℝ) ⟨μ, hμ, rfl⟩
    simpa only [measureReal_def, ENNReal.toReal_ofReal hδ.le] using
      ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  have htail_int : (∫ t in Kᶜ, ‖φ t - g t‖ ∂(μ : Measure ℝ)) ≤ 2 * B * δ := by
    calc
      _ ≤ ∫ _ in Kᶜ, 2 * B ∂(μ : Measure ℝ) :=
        integral_mono hi.integrableOn (integrable_const _) herr
      _ = 2 * B * (μ : Measure ℝ).real Kᶜ := by simp [mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left htailμ (by positivity)
  rw [← integral_add_compl hK.measurableSet hi]
  have hδcancel : δ * (8 * (B + 1)) = ε := div_mul_cancel₀ _ (by positivity)
  have hζcancel : (ε / (4 * ((C : ℝ) + 1))) * (4 * ((C : ℝ) + 1)) = ε :=
    div_mul_cancel₀ _ (by positivity)
  have hζ : 0 ≤ ε / (4 * ((C : ℝ) + 1)) := by positivity
  nlinarith

section Augmentation

variable {E κ : Type*} [MetricSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] [Fintype κ]

def augmentWithFunctions (p : κ → C(E, ℝ)) (f : κ → ℝ → ℝ) (x : E) : E × (κ → ℝ) :=
  (x, fun i ↦ f i (p i x))

omit [SecondCountableTopology E] [Fintype κ] in
theorem measurable_augmentWithFunctions (p : κ → C(E, ℝ)) (f : κ → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) : Measurable (augmentWithFunctions p f) :=
  measurable_id.prodMk (measurable_pi_iff.mpr fun i ↦ (hf i).comp (p i).continuous.measurable)

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] [Fintype κ] in
theorem continuous_augmentWithFunctions (p : κ → C(E, ℝ)) (f : κ → ℝ → ℝ)
    (hf : ∀ i, Continuous (f i)) : Continuous (augmentWithFunctions p f) :=
  continuous_id.prodMk (continuous_pi fun i ↦ (hf i).comp (p i).continuous)

omit [SecondCountableTopology E] in
theorem integral_lipschitz_augmentation_error
    (μ : ProbabilityMeasure E) (p : κ → C(E, ℝ))
    {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hbound : ∀ t, ‖φ t‖ ≤ B)
    (g : κ → ℝ →ᵇ ℝ) (F : (E × (κ → ℝ)) →ᵇ ℝ) {L : ℝ≥0}
    (hF : LipschitzWith L F) :
    ‖(∫ x, F (augmentWithFunctions p (fun _ ↦ φ) x) ∂(μ : Measure E)) -
      ∫ x, F (augmentWithFunctions p (fun i ↦ g i) x) ∂(μ : Measure E)‖ ≤
      (L : ℝ) * ∑ i, ∫ x, ‖φ (p i x) - g i (p i x)‖ ∂(μ : Measure E) := by
  classical
  have hmeas := measurable_augmentWithFunctions p (fun _ ↦ φ) (fun _ ↦ hφ)
  have hcont := continuous_augmentWithFunctions p (fun i ↦ g i) (fun i ↦ (g i).continuous)
  have hi₁ : Integrable (fun x ↦ F (augmentWithFunctions p (fun _ ↦ φ) x))
      (μ : Measure E) :=
    Integrable.of_bound (F.continuous.measurable.comp hmeas).aestronglyMeasurable ‖F‖
      (Eventually.of_forall (fun x ↦ F.norm_coe_le_norm _))
  have hi₂ : Integrable (fun x ↦ F (augmentWithFunctions p (fun i ↦ g i) x))
      (μ : Measure E) := (F.compContinuous ⟨_, hcont⟩).integrable (μ : Measure E)
  have herr (i : κ) : Integrable (fun x ↦ ‖φ (p i x) - g i (p i x)‖) (μ : Measure E) := by
    refine Integrable.of_bound
      (((hφ.comp (p i).continuous.measurable).sub
        ((g i).continuous.comp (p i).continuous).measurable).norm.aestronglyMeasurable)
      (B + ‖g i‖) (Eventually.of_forall fun x ↦ ?_)
    simp only [norm_norm]
    exact (norm_sub_le _ _).trans (add_le_add (hbound _) ((g i).norm_coe_le_norm _))
  have hpoint (x : E) :
      ‖F (augmentWithFunctions p (fun _ ↦ φ) x) -
        F (augmentWithFunctions p (fun i ↦ g i) x)‖ ≤
        (L : ℝ) * ∑ i, ‖φ (p i x) - g i (p i x)‖ := by
    have hd : dist (augmentWithFunctions p (fun _ ↦ φ) x)
        (augmentWithFunctions p (fun i ↦ g i) x) ≤
        ∑ i, ‖φ (p i x) - g i (p i x)‖ := by
      rw [augmentWithFunctions, augmentWithFunctions, dist_prod_same_left]
      apply (dist_pi_le_iff (Finset.sum_nonneg (fun _ _ ↦ norm_nonneg _))).mpr
      intro i
      rw [dist_eq_norm]
      exact Finset.single_le_sum (f := fun j ↦ ‖φ (p j x) - g j (p j x)‖)
        (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
    exact (hF.dist_le_mul _ _).trans (mul_le_mul_of_nonneg_left hd L.coe_nonneg)
  rw [← integral_sub hi₁ hi₂]
  calc
    _ ≤ ∫ x, (L : ℝ) * ∑ i, ‖φ (p i x) - g i (p i x)‖ ∂(μ : Measure E) :=
      norm_integral_le_of_norm_le
        ((integrable_finsetSum _ (fun i _ ↦ herr i)).const_mul (L : ℝ))
        (Eventually.of_forall hpoint)
    _ = _ := by
      rw [integral_const_mul, integral_finsetSum _ (fun i _ ↦ herr i)]

omit [SecondCountableTopology E] in
theorem exists_common_scalar_approx_of_weak_seq
    (μs : ℕ → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (hμ : Tendsto μs atTop (𝓝 μ)) (p : κ → C(E, ℝ)) (C : ℝ≥0)
    (hdom : ∀ n i, (μs n : Measure E).map (p i) ≤ C • (volume : Measure ℝ))
    (hdom_limit : ∀ i, (μ : Measure E).map (p i) ≤ C • (volume : Measure ℝ))
    {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t, ‖φ t‖ ≤ B) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : ℝ →ᵇ ℝ, (∀ t, ‖g t‖ ≤ B) ∧
      (∀ n i, (∫ x, ‖φ (p i x) - g (p i x)‖ ∂(μs n : Measure E)) < ε) ∧
      (∀ i, (∫ x, ‖φ (p i x) - g (p i x)‖ ∂(μ : Measure E)) < ε) := by
  let νs (i : κ) (n : ℕ) : ProbabilityMeasure ℝ :=
    (μs n).map (p i).continuous.measurable.aemeasurable
  let ν (i : κ) : ProbabilityMeasure ℝ := μ.map (p i).continuous.measurable.aemeasurable
  have hν (i : κ) : Tendsto (νs i) atTop (𝓝 (ν i)) :=
    ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ hμ (p i).continuous
  let S : Set (ProbabilityMeasure ℝ) := ⋃ i, insert (ν i) (range (νs i))
  have hS : IsCompact S := isCompact_iUnion fun i ↦ (hν i).isCompact_insert_range
  have htight : IsTightMeasureSet
      ((fun ρ : ProbabilityMeasure ℝ ↦ (ρ : Measure ℝ)) '' S) := by
    apply isTightMeasureSet_of_isCompact_closure
    rwa [hS.isClosed.closure_eq]
  have hdomS : ∀ ρ ∈ S, (ρ : Measure ℝ) ≤ C • (volume : Measure ℝ) := by
    intro ρ hρ
    obtain ⟨i, hi⟩ := mem_iUnion.mp hρ
    rcases hi with hρ | hρ
    · subst ρ
      exact hdom_limit i
    · obtain ⟨n, rfl⟩ := hρ
      exact hdom n i
  obtain ⟨g, hgb, hg⟩ := exists_boundedContinuous_uniform_integral_approx_of_tight
    S htight C hdomS hφ hB hbound hε
  refine ⟨g, hgb, ?_, ?_⟩
  · intro n i
    have h := hg (νs i n) (mem_iUnion.mpr ⟨i, Or.inr ⟨n, rfl⟩⟩)
    change (∫ t, ‖φ t - g t‖ ∂((μs n : Measure E).map (p i))) < ε at h
    rwa [integral_map (p i).continuous.measurable.aemeasurable
      (hφ.sub g.continuous.measurable).norm.aestronglyMeasurable] at h
  · intro i
    have h := hg (ν i) (mem_iUnion.mpr ⟨i, Or.inl rfl⟩)
    change (∫ t, ‖φ t - g t‖ ∂((μ : Measure E).map (p i))) < ε at h
    rwa [integral_map (p i).continuous.measurable.aemeasurable
      (hφ.sub g.continuous.measurable).norm.aestronglyMeasurable] at h

omit [SecondCountableTopology E] in
theorem tendsto_augmented_lipschitz_test_integral_seq
    (μs : ℕ → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (hμ : Tendsto μs atTop (𝓝 μ)) (p : κ → C(E, ℝ)) (C : ℝ≥0)
    (hdom : ∀ n i, (μs n : Measure E).map (p i) ≤ C • (volume : Measure ℝ))
    (hdom_limit : ∀ i, (μ : Measure E).map (p i) ≤ C • (volume : Measure ℝ))
    {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t, ‖φ t‖ ≤ B) (F : (E × (κ → ℝ)) →ᵇ ℝ) {L : ℝ≥0}
    (hF : LipschitzWith L F) :
    Tendsto (fun n ↦ ∫ x, F (augmentWithFunctions p (fun _ ↦ φ) x) ∂(μs n : Measure E))
      atTop (𝓝 (∫ x, F (augmentWithFunctions p (fun _ ↦ φ) x) ∂(μ : Measure E))) := by
  classical
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := ε / (8 * ((L : ℝ) + 1) * ((Fintype.card κ : ℝ) + 1))
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨g, _, hgs, hg⟩ := exists_common_scalar_approx_of_weak_seq
    μs μ hμ p C hdom hdom_limit hφ hB hbound hδ
  have hcoef : (L : ℝ) * ((Fintype.card κ : ℝ) * δ) ≤ ε / 8 := by
    have hc : (L : ℝ) * (Fintype.card κ : ℝ) ≤
        ((L : ℝ) + 1) * ((Fintype.card κ : ℝ) + 1) := by
      nlinarith [L.coe_nonneg, Nat.cast_nonneg (Fintype.card κ) (α := ℝ)]
    have hmul := mul_le_mul_of_nonneg_right hc hδ.le
    have hcancel : δ * (8 * ((L : ℝ) + 1) * ((Fintype.card κ : ℝ) + 1)) = ε :=
      div_mul_cancel₀ _ (by positivity)
    nlinarith
  have happrox (ρ : ProbabilityMeasure E)
      (hρ : ∀ i, (∫ x, ‖φ (p i x) - g (p i x)‖ ∂(ρ : Measure E)) < δ) :
      ‖(∫ x, F (augmentWithFunctions p (fun _ ↦ φ) x) ∂(ρ : Measure E)) -
        ∫ x, F (augmentWithFunctions p (fun _ ↦ g) x) ∂(ρ : Measure E)‖ ≤ ε / 8 := by
    refine (integral_lipschitz_augmentation_error ρ p hφ hbound (fun _ ↦ g) F hF).trans ?_
    calc
      _ ≤ (L : ℝ) * ∑ _ : κ, δ := by
        gcongr with i
        exact (hρ i).le
      _ = (L : ℝ) * ((Fintype.card κ : ℝ) * δ) := by simp
      _ ≤ _ := hcoef
  let G : E →ᵇ ℝ := F.compContinuous
    ⟨augmentWithFunctions p (fun _ ↦ g),
      continuous_augmentWithFunctions p (fun _ ↦ g) (fun _ ↦ g.continuous)⟩
  have hc := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hμ) G
  filter_upwards [(Metric.tendsto_nhds.mp hc) (ε / 2) (by positivity)] with n hn
  have ha := happrox (μs n) (hgs n)
  have hb := happrox μ hg
  change dist (∫ x, F (augmentWithFunctions p (fun _ ↦ g) x) ∂(μs n : Measure E))
    (∫ x, F (augmentWithFunctions p (fun _ ↦ g) x) ∂(μ : Measure E)) < ε / 2 at hn
  rw [dist_eq_norm] at hn ⊢
  have ht := norm_sub_le_norm_sub_add_norm_sub
    (∫ x, F (augmentWithFunctions p (fun _ ↦ φ) x) ∂(μs n : Measure E))
    (∫ x, F (augmentWithFunctions p (fun _ ↦ g) x) ∂(μs n : Measure E))
    (∫ x, F (augmentWithFunctions p (fun _ ↦ φ) x) ∂(μ : Measure E))
  have ht' := norm_sub_le_norm_sub_add_norm_sub
    (∫ x, F (augmentWithFunctions p (fun _ ↦ g) x) ∂(μs n : Measure E))
    (∫ x, F (augmentWithFunctions p (fun _ ↦ g) x) ∂(μ : Measure E))
    (∫ x, F (augmentWithFunctions p (fun _ ↦ φ) x) ∂(μ : Measure E))
  rw [norm_sub_rev (∫ x, F (augmentWithFunctions p (fun _ ↦ g) x)
    ∂(μ : Measure E))] at ht'
  linarith

abbrev DensityBoundedLaw (p : κ → C(E, ℝ)) (C : ℝ≥0) :=
  {μ : ProbabilityMeasure E // ∀ i,
    (μ : Measure E).map (p i) ≤ C • (volume : Measure ℝ)}

def augmentedLaw (p : κ → C(E, ℝ)) {φ : ℝ → ℝ} (hφ : Measurable φ)
    (μ : ProbabilityMeasure E) : ProbabilityMeasure (E × (κ → ℝ)) :=
  μ.map (measurable_augmentWithFunctions p (fun _ ↦ φ) (fun _ ↦ hφ)).aemeasurable

theorem continuous_augmentedLaw_on_densityBoundedLaws
    (p : κ → C(E, ℝ)) (C : ℝ≥0) {φ : ℝ → ℝ} (hφ : Measurable φ)
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ t, ‖φ t‖ ≤ B) :
    Continuous (fun μ : DensityBoundedLaw p C ↦ augmentedLaw p hφ μ.1) := by
  apply continuous_iff_seqContinuous.mpr
  intro μs μ hμ
  have hweak : Tendsto (fun n ↦ (μs n).1) atTop (𝓝 μ.1) :=
    (continuous_subtype_val.tendsto μ).comp hμ
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  rintro F hFb ⟨L, hF⟩
  let F' : (E × (κ → ℝ)) →ᵇ ℝ := ⟨⟨F, hF.continuous⟩, hFb⟩
  have h := tendsto_augmented_lipschitz_test_integral_seq
    (fun n ↦ (μs n).1) μ.1 hweak p C (fun n ↦ (μs n).2) μ.2 hφ hB hbound F' hF
  have hmap (ρ : ProbabilityMeasure E) :
      (∫ y, F y ∂(augmentedLaw p hφ ρ : Measure (E × (κ → ℝ)))) =
        ∫ x, F (augmentWithFunctions p (fun _ ↦ φ) x) ∂(ρ : Measure E) := by
    exact integral_map (measurable_augmentWithFunctions p (fun _ ↦ φ)
      (fun _ ↦ hφ)).aemeasurable hF.continuous.measurable.aestronglyMeasurable
  simpa only [Function.comp_apply, hmap] using h

/-- Bounded measurable coordinate transformations preserve weak convergence under a
uniform scalar density bound. The original state is retained, including any auxiliary weights. -/
theorem tendsto_augmentedLaw_of_density_bound {α : Type*} {l : Filter α}
    (μs : α → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (hμ : Tendsto μs l (𝓝 μ)) (p : κ → C(E, ℝ)) (C : ℝ≥0)
    (hdom : ∀ n i, (μs n : Measure E).map (p i) ≤ C • (volume : Measure ℝ))
    (hdom_limit : ∀ i, (μ : Measure E).map (p i) ≤ C • (volume : Measure ℝ))
    {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t, ‖φ t‖ ≤ B) :
    Tendsto (fun n ↦ augmentedLaw p hφ (μs n)) l (𝓝 (augmentedLaw p hφ μ)) := by
  let G : DensityBoundedLaw p C → ProbabilityMeasure (E × (κ → ℝ)) :=
    fun ρ ↦ augmentedLaw p hφ ρ.1
  have hG : Continuous G := continuous_augmentedLaw_on_densityBoundedLaws p C hφ hB hbound
  have hsub : Tendsto (fun n ↦ (⟨μs n, hdom n⟩ : DensityBoundedLaw p C)) l
      (𝓝 ⟨μ, hdom_limit⟩) := tendsto_subtype_rng.mpr hμ
  exact (hG.tendsto ⟨μ, hdom_limit⟩).comp hsub

theorem scalar_density_bound_of_tendsto {α : Type*} {l : Filter α} [l.NeBot]
    (μs : α → ProbabilityMeasure ℝ) (μ : ProbabilityMeasure ℝ)
    (hμ : Tendsto μs l (𝓝 μ)) (C : ℝ≥0)
    (hdom : ∀ n, (μs n : Measure ℝ) ≤ C • (volume : Measure ℝ)) :
    (μ : Measure ℝ) ≤ C • (volume : Measure ℝ) := by
  apply Measure.le_iff.mpr
  intro s _
  rw [s.measure_eq_iInf_isOpen (C • (volume : Measure ℝ))]
  refine le_iInf fun U ↦ le_iInf fun hsU ↦ le_iInf fun hU ↦ ?_
  refine (measure_mono hsU).trans
    ((ProbabilityMeasure.le_liminf_measure_open_of_tendsto hμ hU).trans ?_)
  apply liminf_le_of_frequently_le'
  exact (Eventually.of_forall (fun n ↦ (hdom n) U)).frequently

theorem tendsto_augmentedLaw_of_source_density_bound {α : Type*} {l : Filter α}
    (μs : α → ProbabilityMeasure E) (μ : ProbabilityMeasure E)
    (hμ : Tendsto μs l (𝓝 μ)) (p : κ → C(E, ℝ)) (C : ℝ≥0)
    (hdom : ∀ n i, (μs n : Measure E).map (p i) ≤ C • (volume : Measure ℝ))
    {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t, ‖φ t‖ ≤ B) :
    Tendsto (fun n ↦ augmentedLaw p hφ (μs n)) l (𝓝 (augmentedLaw p hφ μ)) := by
  rcases l.eq_or_neBot with rfl | hl
  · exact tendsto_bot
  letI := hl
  apply tendsto_augmentedLaw_of_density_bound μs μ hμ p C hdom _ hφ hB hbound
  intro i
  exact scalar_density_bound_of_tendsto
    (fun n ↦ (μs n).map (p i).continuous.measurable.aemeasurable)
    (μ.map (p i).continuous.measurable.aemeasurable)
    (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous μs μ hμ (p i).continuous)
    C (fun n ↦ hdom n i)

theorem tendstoInDistribution_augmented_of_density_bound
    {α Ω' : Type*} {Ω : α → Type*} [∀ a, MeasurableSpace (Ω a)] [MeasurableSpace Ω']
    {l : Filter α} (μs : (a : α) → Measure (Ω a)) [∀ a, IsProbabilityMeasure (μs a)]
    (μ : Measure Ω') [IsProbabilityMeasure μ] (X : (a : α) → Ω a → E) (Z : Ω' → E)
    (hX : TendstoInDistribution X l Z μs μ) (p : κ → C(E, ℝ)) (C : ℝ≥0)
    (hdom : ∀ a i, (μs a).map (fun ω ↦ p i (X a ω)) ≤ C • (volume : Measure ℝ))
    {φ : ℝ → ℝ} (hφ : Measurable φ) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ t, ‖φ t‖ ≤ B) :
    TendstoInDistribution (fun a ω ↦ augmentWithFunctions p (fun _ ↦ φ) (X a ω)) l
      (fun ω ↦ augmentWithFunctions p (fun _ ↦ φ) (Z ω)) μs μ := by
  let νs (a : α) : ProbabilityMeasure E :=
    ⟨(μs a).map (X a), Measure.isProbabilityMeasure_map (hX.forall_aemeasurable a)⟩
  let ν : ProbabilityMeasure E :=
    ⟨μ.map Z, Measure.isProbabilityMeasure_map hX.aemeasurable_limit⟩
  have hνdom (a : α) (i : κ) :
      (νs a : Measure E).map (p i) ≤ C • (volume : Measure ℝ) := by
    dsimp [νs]
    rw [AEMeasurable.map_map_of_aemeasurable (p i).continuous.measurable.aemeasurable
      (hX.forall_aemeasurable a)]
    exact hdom a i
  have hm := measurable_augmentWithFunctions p (fun _ ↦ φ) (fun _ ↦ hφ)
  have hAug := tendsto_augmentedLaw_of_source_density_bound νs ν hX.tendsto p C
    hνdom hφ hB hbound
  refine ⟨fun a ↦ hm.comp_aemeasurable (hX.forall_aemeasurable a),
    hm.comp_aemeasurable hX.aemeasurable_limit, ?_⟩
  convert! hAug using 2
  · apply Subtype.ext
    exact (AEMeasurable.map_map_of_aemeasurable hm.aemeasurable
      (hX.forall_aemeasurable _)).symm
  · apply Subtype.ext
    exact (AEMeasurable.map_map_of_aemeasurable hm.aemeasurable hX.aemeasurable_limit).symm

theorem tendstoInDistribution_augmented_derivative_of_density_bound
    {α Ω' : Type*} {Ω : α → Type*} [∀ a, MeasurableSpace (Ω a)] [MeasurableSpace Ω']
    {l : Filter α} (μs : (a : α) → Measure (Ω a)) [∀ a, IsProbabilityMeasure (μs a)]
    (μ : Measure Ω') [IsProbabilityMeasure μ] (X : (a : α) → Ω a → E) (Z : Ω' → E)
    (hX : TendstoInDistribution X l Z μs μ) (p : κ → C(E, ℝ)) (C : ℝ≥0)
    (hdom : ∀ a i, (μs a).map (fun ω ↦ p i (X a ω)) ≤ C • (volume : Measure ℝ))
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) :
    TendstoInDistribution (fun a ω ↦ augmentWithFunctions p (fun _ ↦ deriv σ) (X a ω)) l
      (fun ω ↦ augmentWithFunctions p (fun _ ↦ deriv σ) (Z ω)) μs μ :=
  tendstoInDistribution_augmented_of_density_bound μs μ X Z hX p C hdom
    (measurable_deriv σ) K.coe_nonneg (activation_derivative_bound hσ)

end Augmentation

end JGH

end

/- Bundled from Definitions/JGH/ProbabilityStability.lean. -/
/-!
Coupling estimates for arbitrary-filter convergence of finite-dimensional laws.
Used in the sequential initialization induction of Jacot--Gabriel--Hongler,
Appendix A.1, PDF pp. 12–13; this is a formal probability bridge.
-/

open MeasureTheory Filter Metric Topology TopologicalSpace
open scoped ENNReal Topology
namespace JGH

theorem map_measure_le_thickening_add {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure Ω) (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    (δ : ℝ) (B : Set E) (hB : MeasurableSet B) :
    μ.map X B ≤ μ.map Y (thickening δ B) + μ {ω | δ ≤ dist (X ω) (Y ω)} := by
  rw [Measure.map_apply hX hB, Measure.map_apply hY isOpen_thickening.measurableSet]
  calc
    _ ≤ μ ((Y ⁻¹' thickening δ B) ∪ {ω | δ ≤ dist (X ω) (Y ω)}) := by
      apply measure_mono
      intro ω hω
      by_cases hd : δ ≤ dist (X ω) (Y ω)
      · exact Or.inr hd
      · exact Or.inl (mem_thickening_iff.mpr ⟨X ω, hω, by
          simpa [dist_comm] using lt_of_not_ge hd⟩)
    _ ≤ _ := measure_union_le _ _

theorem levyProkhorovEDist_map_le {Ω E : Type*} [MeasurableSpace Ω]
    [PseudoMetricSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure Ω) (X Y : Ω → E) (hX : Measurable X) (hY : Measurable Y)
    {δ : ℝ} (hδ : 0 ≤ δ) :
    levyProkhorovEDist (μ.map X) (μ.map Y) ≤
      max (ENNReal.ofReal δ) (μ {ω | δ ≤ dist (X ω) (Y ω)}) := by
  apply levyProkhorovEDist_le_of_forall
  intro ε B hε hεtop hB
  have hδε : δ < ε.toReal := (ENNReal.ofReal_lt_iff_lt_toReal hδ hεtop.ne).mp
    (lt_of_le_of_lt (le_max_left _ _) hε)
  have hbad : μ {ω | ε.toReal ≤ dist (X ω) (Y ω)} ≤ ε :=
    (measure_mono fun ω hω ↦ hδε.le.trans hω).trans
      ((le_max_right _ _).trans hε.le)
  constructor
  · exact (map_measure_le_thickening_add μ X Y hX hY ε.toReal B hB).trans
      (add_le_add le_rfl hbad)
  · have hbad' : μ {ω | ε.toReal ≤ dist (Y ω) (X ω)} ≤ ε := by
      simpa only [dist_comm] using hbad
    exact (map_measure_le_thickening_add μ Y X hY hX ε.toReal B hB).trans
      (add_le_add le_rfl hbad')

theorem levyProkhorovEDist_map_tendsto_zero {ι E : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] [PseudoMetricSpace E] [MeasurableSpace E]
    [OpensMeasurableSpace E] (μ : ∀ i, Measure (Ω i))
    (X Y : ∀ i, Ω i → E) (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {l : Filter ι}
    (hclose : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun i ↦ μ i {ω | δ ≤ dist (X i ω) (Y i ω)}) l (𝓝 0)) :
    Tendsto (fun i ↦ levyProkhorovEDist ((μ i).map (X i)) ((μ i).map (Y i))) l (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  by_cases htop : ε = ∞
  · simp [htop]
  have hδ : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  filter_upwards [ENNReal.tendsto_nhds_zero.mp (hclose ε.toReal hδ) ε hε] with i hi
  refine (levyProkhorovEDist_map_le (μ i) (X i) (Y i) (hX i) (hY i) hδ.le).trans ?_
  exact max_le (by simp [ENNReal.ofReal_toReal, htop]) hi

noncomputable def probabilityLaw {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → E) (hX : Measurable X) :
    ProbabilityMeasure E := ⟨μ.map X, Measure.isProbabilityMeasure_map hX.aemeasurable⟩

theorem tendsto_law_of_close {ι E : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] [PseudoMetricSpace E] [SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E] (μ : ∀ i, Measure (Ω i))
    [∀ i, IsProbabilityMeasure (μ i)] (X Y : ∀ i, Ω i → E)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i))
    {l : Filter ι} {ν : ProbabilityMeasure E}
    (hclose : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun i ↦ μ i {ω | δ ≤ dist (X i ω) (Y i ω)}) l (𝓝 0))
    (hlim : Tendsto (fun i ↦ probabilityLaw (μ i) (Y i) (hY i)) l (𝓝 ν)) :
    Tendsto (fun i ↦ probabilityLaw (μ i) (X i) (hX i)) l (𝓝 ν) := by
  let e := LevyProkhorov.probabilityMeasureHomeomorph (Ω := E)
  have hLP := levyProkhorovEDist_map_tendsto_zero μ X Y hX hY hclose
  have hd : Tendsto (fun i ↦ dist
      (e (probabilityLaw (μ i) (Y i) (hY i)))
      (e (probabilityLaw (μ i) (X i) (hX i))))
      l (𝓝 0) := by
    simpa only [LevyProkhorov.dist_probabilityMeasure_def, levyProkhorovDist,
      levyProkhorovEDist_comm, ENNReal.toReal_zero, probabilityLaw] using
      (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hLP
  have ht := ((e.continuous.tendsto ν).comp hlim).congr_dist hd
  simpa using (e.symm.continuous.tendsto (e ν)).comp ht

/-- Slutsky's joint-law conclusion for varying sample spaces and an arbitrary filter. -/
theorem tendstoInDistribution_prod_const {ι E F Ω' : Type*} {Ω : ι → Type*}
    [∀ i, MeasurableSpace (Ω i)] [MeasurableSpace Ω']
    [PseudoMetricSpace E] [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E]
    [PseudoMetricSpace F] [SecondCountableTopology F] [MeasurableSpace F] [BorelSpace F]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (μ' : Measure Ω') [IsProbabilityMeasure μ']
    (X : ∀ i, Ω i → E) (Y : ∀ i, Ω i → F) (Z : Ω' → E) (c : F)
    (hX : ∀ i, Measurable (X i)) (hY : ∀ i, Measurable (Y i)) {l : Filter ι}
    (hlim : TendstoInDistribution X l Z μ μ')
    (hclose : ∀ δ : ℝ, 0 < δ →
      Tendsto (fun i ↦ μ i {ω | δ ≤ dist (Y i ω) c}) l (𝓝 0)) :
    TendstoInDistribution (fun i ω ↦ (X i ω, Y i ω)) l (fun ω ↦ (Z ω, c)) μ μ' := by
  have hp := hlim.continuous_comp
    (g := fun x : E ↦ (x, c)) (continuous_id.prodMk continuous_const)
  refine ⟨fun i ↦ ((hX i).prodMk (hY i)).aemeasurable, hp.aemeasurable_limit, ?_⟩
  exact tendsto_law_of_close μ
    (fun i ω ↦ (X i ω, Y i ω)) (fun i ω ↦ (X i ω, c))
    (fun i ↦ (hX i).prodMk (hY i)) (fun i ↦ (hX i).prodMk measurable_const)
    (fun δ hδ ↦ by simpa only [dist_prod_same_left] using hclose δ hδ) hp.tendsto

end JGH

/- Bundled from Definitions/JGH/NTKLaw.lean. -/
/-!
Jacot--Gabriel--Hongler, arXiv:1806.07572v4, Appendix A.1,
Theorem 1 proof, PDF pp. 12--13. The finite matrix NTK law is assembled using
the exact derivative recurrence, the Gaussian initialization limit, and the
outer-width strong law. No differentiability beyond Lipschitz continuity is assumed.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators Topology ENNReal NNReal
namespace JGH

def initializedNTK {h N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) (w : Fin h → ℕ)
    (θ : Parameters (h + 1) (widths d q w)) : EuclideanSpace ℝ (NTKEntryIndex N q) :=
  WithLp.toLp 2 (fun ab ↦ finiteNTK (h + 1) (widths d q w) σ β θ
    (inputForWidths d q w (X ab.1.1)) (inputForWidths d q w (X ab.2.1))
    (outputForWidths d q w ab.1.2) (outputForWidths d q w ab.2.2))

theorem measurable_parameterDerivative (L : ℕ) (width : ℕ → ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (x : Fin (width 0) → ℝ) (k : Fin (width L)) (p : ParameterIndex L width) :
    Measurable (fun θ ↦ parameterDerivative L width σ β θ x k p) := by
  classical
  exact measurable_fderiv_apply_const ℝ (fun θ ↦ network L width σ β θ x k)
    (Pi.single p 1)

theorem measurable_finiteNTK (L : ℕ) (width : ℕ → ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (x y : Fin (width 0) → ℝ) (k k' : Fin (width L)) :
    Measurable (fun θ ↦ finiteNTK L width σ β θ x y k k') := by
  unfold finiteNTK
  exact Finset.measurable_sum _ (fun p _ ↦
    (measurable_parameterDerivative L width σ β x k p).mul
      (measurable_parameterDerivative L width σ β y k' p))

theorem measurable_initializedNTK {h N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) (w : Fin h → ℕ) :
    Measurable (initializedNTK d q σ β X w) := by
  apply (WithLp.measurable_toLp 2 _).comp
  apply measurable_pi_lambda
  intro ab
  exact measurable_finiteNTK _ _ _ _ _ _ _ _

def initializedNTKLaw {h N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) (w : Fin h → ℕ) :
    ProbabilityMeasure (EuclideanSpace ℝ (NTKEntryIndex N q)) :=
  probabilityLaw (initialization (h + 1) (widths d q w)) (initializedNTK d q σ β X w)
    (measurable_initializedNTK d q σ β X w)

theorem initializedNTK_zero {N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) (w : Fin 0 → ℕ) (θ : Parameters 1 (widths d q w)) :
    initializedNTK d q σ β X w θ = deterministicNTKVector d q σ β 0 X := by
  ext ab
  exact finiteNTK_widths_zero d q σ β w θ _ _ _ _

abbrev UpperNTKState (N n q : ℕ) :=
  (EuclideanSpace ℝ (Fin N × Fin n) × EuclideanSpace ℝ (NTKEntryIndex N n)) ×
    EuclideanSpace ℝ (Fin q × Fin n)

def upperNTKAugmented {N : ℕ} (n q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (z : UpperNTKState N n q × ((Fin N × Fin n) → ℝ)) :
    EuclideanSpace ℝ (NTKEntryIndex N q) :=
  WithLp.toLp 2 (fun ab ↦
    (∑ i : Fin n, ∑ j : Fin n,
      (z.1.2 (ab.1.2, i) * z.2 (ab.1.1, i)) *
      (z.1.2 (ab.2.2, j) * z.2 (ab.2.1, j)) *
      z.1.1.2 ((ab.1.1, i), (ab.2.1, j))) / n +
    if ab.1.2 = ab.2.2 then
      (∑ i : Fin n, σ (z.1.1.1 (ab.1.1, i)) * σ (z.1.1.1 (ab.2.1, i))) / n +
        β ^ 2 else 0)

theorem continuous_upperNTKAugmented {N : ℕ} (n q : ℕ) {σ : ℝ → ℝ}
    (hσ : Continuous σ) (β : ℝ) :
    Continuous (upperNTKAugmented (N := N) n q σ β) := by
  unfold upperNTKAugmented
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro ab
  split_ifs <;> fun_prop

def upperNTKProjection {N : ℕ} (n q : ℕ) (i : Fin N × Fin n) :
    C(UpperNTKState N n q, ℝ) :=
  ⟨fun z ↦ z.1.1 i, by fun_prop⟩

def upperNTK {N : ℕ} (n q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (z : UpperNTKState N n q) : EuclideanSpace ℝ (NTKEntryIndex N q) :=
  upperNTKAugmented n q σ β
    (augmentWithFunctions (upperNTKProjection n q) (fun _ ↦ deriv σ) z)

theorem measurable_upperNTK {N : ℕ} (n q : ℕ) {σ : ℝ → ℝ}
    (hσ : Continuous σ) (β : ℝ) : Measurable (upperNTK (N := N) n q σ β) :=
  (continuous_upperNTKAugmented n q hσ β).measurable.comp
    (measurable_augmentWithFunctions _ _ (fun _ ↦ measurable_deriv σ))

def lastLayerWeightIndex (n q : ℕ) (a : Fin q × Fin n) :
    ParameterIndex 1 (widths n q Fin.elim0) :=
  ⟨0, outputForWidths n q Fin.elim0 a.1,
    some ⟨a.2.val, by simpa [widths] using a.2.isLt⟩⟩

theorem lastLayerWeightIndex_injective (n q : ℕ) :
    Function.Injective (lastLayerWeightIndex n q) := by
  intro a b hab
  have h := (Sigma.mk.inj hab).2
  have hh := eq_of_heq h
  have hk := congrArg (fun p ↦ p.1.val) hh
  have hi := congrArg (fun p ↦ p.2.map Fin.val) hh
  apply Prod.ext
  · exact Fin.ext hk
  · apply Fin.ext
    simpa only [lastLayerWeightIndex, Option.map_some, Option.some.injEq] using hi

def lastLayerWeights (n q : ℕ) (θ : Parameters 1 (widths n q Fin.elim0)) :
    EuclideanSpace ℝ (Fin q × Fin n) :=
  WithLp.toLp 2 (fun a ↦ θ (lastLayerWeightIndex n q a))

theorem continuous_lastLayerWeights (n q : ℕ) : Continuous (lastLayerWeights n q) := by
  unfold lastLayerWeights
  fun_prop

theorem map_lastLayerWeights (n q : ℕ) :
    (initialization 1 (widths n q Fin.elim0)).map (lastLayerWeights n q) =
      multivariateGaussian 0 (1 : Matrix (Fin q × Fin n) (Fin q × Fin n) ℝ) := by
  have hind : iIndepFun (fun a : Fin q × Fin n ↦
      fun θ : Parameters 1 (widths n q Fin.elim0) ↦ θ (lastLayerWeightIndex n q a))
      (initialization 1 (widths n q Fin.elim0)) :=
    (iIndepFun_pi (fun _ ↦ aemeasurable_id)).precomp (lastLayerWeightIndex_injective n q)
  have hm := hind.map_fun_eq_pi_map (fun a ↦ (measurable_pi_apply _).aemeasurable)
  have he (a : Fin q × Fin n) :
      (initialization 1 (widths n q Fin.elim0)).map
        (fun θ ↦ θ (lastLayerWeightIndex n q a)) = gaussianReal 0 1 :=
    (measurePreserving_eval (fun _ ↦ gaussianReal 0 1) (lastLayerWeightIndex n q a)).map_eq
  simp_rw [he] at hm
  unfold lastLayerWeights
  change Measure.map ((WithLp.toLp 2) ∘
    (fun θ : Parameters 1 (widths n q Fin.elim0) ↦
      fun a : Fin q × Fin n ↦ θ (lastLayerWeightIndex n q a))) _ = _
  rw [← Measure.map_map (WithLp.measurable_toLp 2 _) (by fun_prop), hm,
    map_pi_eq_stdGaussian, multivariateGaussian_zero_one]

end JGH

end

/- Bundled from Definitions/JGH/NTKOuterLaw.lean. -/
/-!
Exact finite-prefix law and outer-width limit for the NTK induction in
Jacot--Gabriel--Hongler, arXiv:1806.07572v4, Appendix A.1, PDF p. 13.
The independent Gaussian neuron samples realize the paper's final law-of-large-numbers step.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators Topology ENNReal NNReal
namespace JGH

def limitingUpperNTK {N : ℕ} (d n q : ℕ) (σ : ℝ → ℝ) (β : ℝ) (h : ℕ)
    (X : Fin N → Input d)
    (z : EuclideanSpace ℝ (Fin N × Fin n) × EuclideanSpace ℝ (Fin q × Fin n)) :
    EuclideanSpace ℝ (NTKEntryIndex N q) :=
  upperNTK n q σ β ((z.1, deterministicNTKVector d n σ β h X), z.2)

theorem measurable_limitingUpperNTK {N : ℕ} (d n q : ℕ) {σ : ℝ → ℝ}
    (hσ : Continuous σ) (β : ℝ) (h : ℕ) (X : Fin N → Input d) :
    Measurable (limitingUpperNTK d n q σ β h X) :=
  (measurable_upperNTK n q hσ β).comp ((measurable_fst.prodMk measurable_const).prodMk
    measurable_snd)

def limitingUpperNTKLaw {N : ℕ} (d n q : ℕ) (σ : ℝ → ℝ)
    (hσ : Continuous σ) (β : ℝ) (h : ℕ) (X : Fin N → Input d) :
    ProbabilityMeasure (EuclideanSpace ℝ (NTKEntryIndex N q)) :=
  probabilityLaw ((outputGaussian d n σ β h X).prod
    (multivariateGaussian 0 (1 : Matrix (Fin q × Fin n) (Fin q × Fin n) ℝ)))
    (limitingUpperNTK d n q σ β h X) (measurable_limitingUpperNTK d n q hσ β h X)

def neuronPrefix {N q : ℕ} (n : ℕ)
    (ω : ℕ → EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin q)) :
    EuclideanSpace ℝ (Fin N × Fin n) × EuclideanSpace ℝ (Fin q × Fin n) :=
  (gaussianColumnsMap (fun a : Fin n ↦ (ω a).1),
    gaussianColumnsMap (fun a : Fin n ↦ (ω a).2))

theorem measurePreserving_neuronPrefix {N q : ℕ}
    (C : Matrix (Fin N) (Fin N) ℝ) (hC : C.PosSemidef) (n : ℕ) :
    MeasurePreserving (neuronPrefix (N := N) (q := q) n)
      (Measure.infinitePi (fun _ : ℕ ↦ ntkNeuronLaw C))
      ((multivariateGaussian 0 (fun a b : Fin N × Fin n ↦
          if a.2 = b.2 then C a.1 b.1 else 0)).prod
        (multivariateGaussian 0 (1 : Matrix (Fin q × Fin n) (Fin q × Fin n) ℝ))) := by
  have hp : MeasurePreserving
      (MeasurableEquiv.arrowProdEquivProdArrow (EuclideanSpace ℝ (Fin N))
        (EuclideanSpace ℝ (Fin q)) (Fin n))
      (Measure.pi (fun _ : Fin n ↦ ntkNeuronLaw C))
      ((Measure.pi (fun _ : Fin n ↦ multivariateGaussian 0 C)).prod
        (Measure.pi (fun _ : Fin n ↦ multivariateGaussian 0 (1 : Matrix (Fin q) (Fin q) ℝ)))) :=
    measurePreserving_arrowProdEquivProdArrow _ _ _ _ _
  have hfirst : MeasurePreserving (gaussianColumnsMap (ι := Fin N) (κ := Fin n))
      (Measure.pi (fun _ : Fin n ↦ multivariateGaussian 0 C))
      (multivariateGaussian 0 (fun a b : Fin N × Fin n ↦
        if a.2 = b.2 then C a.1 b.1 else 0)) :=
    ⟨(gaussianColumnsMap (ι := Fin N) (κ := Fin n)).measurable, map_gaussianColumns hC⟩
  have hsecond : MeasurePreserving (gaussianColumnsMap (ι := Fin q) (κ := Fin n))
      (Measure.pi (fun _ : Fin n ↦ multivariateGaussian 0 (1 : Matrix (Fin q) (Fin q) ℝ)))
      (multivariateGaussian 0 (1 : Matrix (Fin q × Fin n) (Fin q × Fin n) ℝ)) := by
    refine ⟨(gaussianColumnsMap (ι := Fin q) (κ := Fin n)).measurable, ?_⟩
    rw [map_gaussianColumns Matrix.PosSemidef.one]
    congr 1
    ext a b
    simp only [Matrix.one_apply]
    by_cases h : a.2 = b.2 <;> by_cases h' : a.1 = b.1 <;>
      simp [h, h', Prod.ext_iff, and_comm]
  exact ((hfirst.prod hsecond).comp hp).comp (measurePreserving_iidPrefix (ntkNeuronLaw C) n)

theorem limitingUpperNTK_neuronPrefix {N q : ℕ} (d : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (h n : ℕ) (X : Fin N → Input d)
    (ω : ℕ → EuclideanSpace ℝ (Fin N) × EuclideanSpace ℝ (Fin q)) :
    limitingUpperNTK d (n + 1) q σ β h X (neuronPrefix (n + 1) ω) =
      outerNTKVector d σ β h X n ω := by
  ext ab
  simp only [limitingUpperNTK, upperNTK, upperNTKAugmented, augmentWithFunctions,
    upperNTKProjection, ContinuousMap.coe_mk, deterministicNTKVector, neuronPrefix,
    gaussianColumnsMap_apply, outerNTKVector, empiricalOuterNTK]
  have hs : (∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
      ((ω i).2 ab.1.2 * deriv σ ((ω i).1 ab.1.1)) *
      ((ω j).2 ab.2.2 * deriv σ ((ω j).1 ab.2.1)) *
      (if i = j then limitingNTK d σ β h (X ab.1.1) (X ab.2.1) else 0)) =
      limitingNTK d σ β h (X ab.1.1) (X ab.2.1) *
        ∑ i : Fin (n + 1), derivativeNeuronFeature σ ab.1.1 ab.2.1 ab.1.2 ab.2.2 (ω i) := by
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    unfold derivativeNeuronFeature
    ring
  rw [hs]
  rw [Fin.sum_univ_eq_sum_range (fun i ↦
    derivativeNeuronFeature σ ab.1.1 ab.2.1 ab.1.2 ab.2.2 (ω i)),
    Fin.sum_univ_eq_sum_range (fun i ↦ σ ((ω i).1 ab.1.1) * σ ((ω i).1 ab.2.1))]
  ring

theorem limitingUpperNTKLaw_tendsto {N : ℕ} (d q : ℕ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (β : ℝ) (h : ℕ) (X : Fin N → Input d) :
    Tendsto (fun n ↦ limitingUpperNTKLaw d (n + 1) q σ hσ.continuous β h X) atTop
      (𝓝 (⟨Measure.dirac (deterministicNTKVector d q σ β (h + 1) X), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (NTKEntryIndex N q)))) := by
  have ht := (outerNTKVector_tendstoInDistribution (q := q) d hσ β h X).tendsto
  simp only [Measure.map_id] at ht
  convert ht using 1
  ext n : 1
  apply Subtype.ext
  dsimp [limitingUpperNTKLaw, probabilityLaw, outputGaussian]
  have hmap := (measurePreserving_neuronPrefix (q := q) _
    (covarianceKernel_posSemidef d hσ β h N X) (n + 1)).map_eq
  simp only [Matrix.of_apply] at hmap
  rw [← hmap, Measure.map_map (measurable_limitingUpperNTK _ _ _ hσ.continuous _ _ _)
      (by unfold neuronPrefix; fun_prop)]
  congr 1
  funext ω
  exact limitingUpperNTK_neuronPrefix d σ β h n X ω

end JGH

end

/- Bundled from Definitions/JGH/NTKDensity.lean. -/
/-!
Scalar density domination preserved when adjoining the lower-layer tangent kernel and independent
last-layer weights. This is a formal bridge for Jacot--Gabriel--Hongler, Appendix A.1,
PDF pp. 12–13, using the paper's positive Gaussian bias and the unchanged Lipschitz activation.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace JGH

def biasDensityBound (β : ℝ) : ℝ≥0 :=
  Real.toNNReal ((Real.sqrt (2 * Real.pi * β ^ 2))⁻¹)

theorem initializedOutput_scalar_density_bound {h N : ℕ} (d q : ℕ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) {β : ℝ} (hβ : 0 < β)
    (X : Fin N → Input d) (w : Fin h → ℕ) (a : Fin N × Fin q) :
    (initialization (h + 1) (widths d q w)).map
        (fun θ ↦ initializedOutput d q σ β X w θ a) ≤
      (biasDensityBound β : ℝ≥0∞) • (volume : Measure ℝ) := by
  simpa only [initializedOutput, biasDensityBound, ENNReal.coe_toNNReal] using
    network_scalar_density_bound (h + 1) (Nat.succ_pos h) (widths d q w) hσ hβ
      (inputForWidths d q w (X a.1)) (outputForWidths d q w a.2)

/-- A scalar component ignores all adjoined variables; its law is therefore unchanged. -/
theorem scalar_map_adjoin_prod {Ω Λ E F G : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace G]
    (P : Measure Ω) (Q : Measure Λ) [SFinite P] [IsProbabilityMeasure Q]
    (X : Ω → E) (Y : Ω → F) (W : Λ → G) (p : E → ℝ)
    (hpX : Measurable (fun ω ↦ p (X ω))) :
    (P.prod Q).map (fun z ↦ p (((X z.1, Y z.1), W z.2).1.1)) =
      P.map (fun ω ↦ p (X ω)) := by
  change (P.prod Q).map ((fun ω ↦ p (X ω)) ∘ Prod.fst) = _
  rw [← Measure.map_map hpX measurable_fst, Measure.map_fst_prod,
    measure_univ, one_smul]

theorem scalar_density_bound_adjoin_prod {Ω Λ E F G : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Λ] [MeasurableSpace E]
    [MeasurableSpace F] [MeasurableSpace G]
    (P : Measure Ω) (Q : Measure Λ) [SFinite P] [IsProbabilityMeasure Q]
    (X : Ω → E) (Y : Ω → F) (W : Λ → G) (p : E → ℝ)
    (hpX : Measurable (fun ω ↦ p (X ω))) (C : ℝ≥0)
    (hdom : P.map (fun ω ↦ p (X ω)) ≤ (C : ℝ≥0∞) • (volume : Measure ℝ)) :
    (P.prod Q).map (fun z ↦ p (((X z.1, Y z.1), W z.2).1.1)) ≤
      (C : ℝ≥0∞) • (volume : Measure ℝ) := by
  rw [scalar_map_adjoin_prod P Q X Y W p hpX]
  exact hdom

end JGH

end

/- Bundled from Definitions/JGH/DiracTail.lean. -/
/-!
Weak convergence to a deterministic value gives vanishing probabilities of closed positive-radius
tails. This arbitrary-filter bridge is used for the final bad-event statement in
Jacot--Gabriel--Hongler, Theorem 1, PDF p. 5, and Appendix A.1, PDF pp. 12–13.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
namespace JGH

theorem tendsto_measure_dist_ge_of_tendsto_dirac {ι E : Type*}
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    {l : Filter ι} (μ : ι → ProbabilityMeasure E) (c : E)
    (hμ : Tendsto μ l (𝓝 (⟨Measure.dirac c, inferInstance⟩ : ProbabilityMeasure E)))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun i ↦ (μ i : Measure E) {x | ε ≤ dist x c}) l (𝓝 0) := by
  let s : Set E := {x | ε ≤ dist x c}
  have hs : IsClosed s := isClosed_le continuous_const (continuous_id.dist continuous_const)
  have hc : c ∉ s := by simp [s, hε.not_ge]
  have hf : c ∉ frontier s := fun h ↦ hc (hs.frontier_subset h)
  have hzero : Measure.dirac c (frontier s) = 0 := by
    rw [Measure.dirac_apply' _ isClosed_frontier.measurableSet]
    exact Set.indicator_of_notMem hf _
  have h := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hμ hzero
  change Tendsto (fun i ↦ (μ i : Measure E) s) l (𝓝 (Measure.dirac c s)) at h
  rw [Measure.dirac_apply' _ hs.measurableSet, Set.indicator_of_notMem hc] at h
  exact h

theorem tendsto_probability_dist_ge_of_law_tendsto_dirac {ι E : Type*}
    {Ω : ι → Type*} [∀ i, MeasurableSpace (Ω i)]
    [PseudoMetricSpace E] [MeasurableSpace E] [BorelSpace E]
    (μ : ∀ i, Measure (Ω i)) [∀ i, IsProbabilityMeasure (μ i)]
    (X : ∀ i, Ω i → E) (hX : ∀ i, Measurable (X i)) {l : Filter ι} (c : E)
    (hlim : Tendsto (fun i ↦ probabilityLaw (μ i) (X i) (hX i)) l
      (𝓝 (⟨Measure.dirac c, inferInstance⟩ : ProbabilityMeasure E)))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun i ↦ μ i {ω | ε ≤ dist (X i ω) c}) l (𝓝 0) := by
  have h := tendsto_measure_dist_ge_of_tendsto_dirac
    (fun i ↦ probabilityLaw (μ i) (X i) (hX i)) c hlim hε
  have hs : MeasurableSet {x : E | ε ≤ dist x c} :=
    (isClosed_le continuous_const (continuous_id.dist continuous_const)).measurableSet
  simpa only [probabilityLaw, ProbabilityMeasure.coe_mk, Measure.map_apply (hX _) hs,
    Set.preimage_setOf_eq] using h

end JGH

/- Bundled from Definitions/JGH/NTKTail.lean. -/
/-!
The finite-dataset bad-event formulation of Jacot--Gabriel--Hongler, Theorem 1,
PDF p. 5, follows from convergence of the full NTK matrix law to its deterministic limit.
This is a formal bridge; no independence of different entries is required.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal
namespace JGH

theorem ntkBadProbability_le_dist_tail {h N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) (ε : ℝ) (w : Fin h → ℕ) :
    ntkBadProbability d q σ β X ε w ≤
      initialization (h + 1) (widths d q w) {θ |
        ε ≤ dist (initializedNTK d q σ β X w θ) (deterministicNTKVector d q σ β h X)} := by
  apply measure_mono
  intro θ hθ
  obtain ⟨i, j, k, k', hentry⟩ := hθ
  have he := PiLp.norm_apply_le (p := (2 : ENNReal))
    (initializedNTK d q σ β X w θ - deterministicNTKVector d q σ β h X)
    ((i, k), (j, k'))
  change ε ≤ dist (initializedNTK d q σ β X w θ) (deterministicNTKVector d q σ β h X)
  rw [dist_eq_norm]
  exact hentry.le.trans (by simpa [initializedNTK, deterministicNTKVector, Real.norm_eq_abs] using he)

theorem ntkBadProbability_tendsto_of_law_tendsto_dirac {h N : ℕ}
    (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ) (X : Fin N → Input d)
    {l : Filter (Fin h → ℕ)}
    (hlim : Tendsto (initializedNTKLaw d q σ β X) l
      (𝓝 (⟨Measure.dirac (deterministicNTKVector d q σ β h X), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (NTKEntryIndex N q)))))
    {ε : ℝ} (hε : 0 < ε) :
    Tendsto (ntkBadProbability d q σ β X ε) l (𝓝 0) := by
  have ht := tendsto_probability_dist_ge_of_law_tendsto_dirac
    (fun w ↦ initialization (h + 1) (widths d q w))
    (initializedNTK d q σ β X) (measurable_initializedNTK d q σ β X)
    (deterministicNTKVector d q σ β h X) hlim hε
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht
    (fun _ ↦ bot_le) (ntkBadProbability_le_dist_tail d q σ β X ε)

end JGH

end

/- Bundled from Definitions/JGH/NTKTransport.lean. -/
/-!
Parameter-coordinate invariance for the finite-width NTK in Jacot--Gabriel--Hongler,
arXiv:1806.07572v4, Appendix A.1, PDF pp. 12--13.
The derivative identity is unconditional: a continuous linear equivalence also preserves
the nondifferentiable cases where Mathlib totalizes the derivative to zero.
-/

noncomputable section
open scoped BigOperators
namespace JGH

def transportParametersLinear {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) : Parameters L v ≃L[ℝ] Parameters L w :=
  ContinuousLinearEquiv.piCongrLeft ℝ (fun _ ↦ ℝ) (parameterIndexWidthEquiv hvw)

lemma transportParametersLinear_eq {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) (θ : Parameters L v) :
    transportParametersLinear hvw θ = transportParameters hvw θ := rfl

@[simp] lemma transportParametersLinear_apply_index {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) (θ : Parameters L v) (p : ParameterIndex L v) :
    transportParametersLinear hvw θ (parameterIndexWidthEquiv hvw p) = θ p := by
  exact MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ ↦ ℝ)
    (parameterIndexWidthEquiv hvw) θ p

@[simp] lemma transportParametersLinear_single {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) (p : ParameterIndex L v) :
    transportParametersLinear hvw (Pi.single p 1) =
      Pi.single (parameterIndexWidthEquiv hvw p) 1 := by
  classical
  ext q
  obtain ⟨q, rfl⟩ := (parameterIndexWidthEquiv hvw).surjective q
  simp [Pi.single_apply]

lemma parameterDerivative_transport {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters L v) (x : Fin (v 0) → ℝ) (k : Fin (v L)) (p : ParameterIndex L v) :
    parameterDerivative L w σ β (transportParameters hvw θ)
      (fun i ↦ x (Fin.cast (hvw 0 (Nat.zero_le L)).symm i))
      (Fin.cast (hvw L le_rfl) k) (parameterIndexWidthEquiv hvw p) =
        parameterDerivative L v σ β θ x k p := by
  classical
  let f : Parameters L w → ℝ := fun η ↦ network L w σ β η
    (fun i ↦ x (Fin.cast (hvw 0 (Nat.zero_le L)).symm i)) (Fin.cast (hvw L le_rfl) k)
  have heq : f ∘ transportParametersLinear hvw = fun η ↦ network L v σ β η x k := by
    funext η
    exact network_transport hvw σ β η x k
  have h := (transportParametersLinear hvw).comp_right_fderiv (f := f) (x := θ)
  rw [heq] at h
  have hp := congrArg (fun D : Parameters L v →L[ℝ] ℝ ↦ D (Pi.single p 1)) h
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    transportParametersLinear_single] at hp
  exact hp.symm

lemma finiteNTK_transport {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters L v) (x y : Fin (v 0) → ℝ) (k k' : Fin (v L)) :
    finiteNTK L w σ β (transportParameters hvw θ)
      (fun i ↦ x (Fin.cast (hvw 0 (Nat.zero_le L)).symm i))
      (fun i ↦ y (Fin.cast (hvw 0 (Nat.zero_le L)).symm i))
      (Fin.cast (hvw L le_rfl) k) (Fin.cast (hvw L le_rfl) k') =
        finiteNTK L v σ β θ x y k k' := by
  classical
  unfold finiteNTK
  rw [← (parameterIndexWidthEquiv hvw).sum_comp]
  apply Finset.sum_congr rfl
  intro p _
  rw [parameterDerivative_transport, parameterDerivative_transport]

lemma finiteNTK_transport_apply {L : ℕ} {v w : ℕ → ℕ}
    (hvw : ∀ l, l ≤ L → v l = w l) (σ : ℝ → ℝ) (β : ℝ)
    (θ : Parameters L v) (x y : Fin (v 0) → ℝ) (k k' : Fin (w L)) :
    finiteNTK L w σ β (transportParameters hvw θ)
      (fun i ↦ x (Fin.cast (hvw 0 (Nat.zero_le L)).symm i))
      (fun i ↦ y (Fin.cast (hvw 0 (Nat.zero_le L)).symm i)) k k' =
        finiteNTK L v σ β θ x y
          (Fin.cast (hvw L le_rfl).symm k) (Fin.cast (hvw L le_rfl).symm k') := by
  simpa using finiteNTK_transport hvw σ β θ x y
    (Fin.cast (hvw L le_rfl).symm k) (Fin.cast (hvw L le_rfl).symm k')

end JGH

end

/- Bundled from Definitions/JGH/NTKSplit.lean. -/
/-!
The actual-network NTK recurrence under the measure-preserving width split.
Jacot--Gabriel--Hongler, Appendix A.1, PDF p. 13, Theorem 1 proof.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators NNReal
namespace JGH

theorem initializedNTK_snoc_split_ae {h N : ℕ} (d q : ℕ) {σ : ℝ → ℝ}
    {K : ℝ≥0} (hσ : LipschitzWith K σ) {β : ℝ} (hβ : 0 < β)
    (X : Fin N → Input d) (w : Fin h → ℕ) (n : ℕ) :
    ∀ᵐ θ ∂initialization (h + 2) (widths d q (Fin.snoc w n)),
      initializedNTK d q σ β X (Fin.snoc w n) θ =
        upperNTK (n + 1) q σ β
          ((initializedOutput d (n + 1) σ β X w (splitWidthParameters d q w n θ).1,
            initializedNTK d (n + 1) σ β X w (splitWidthParameters d q w n θ).1),
            lastLayerWeights (n + 1) q (splitWidthParameters d q w n θ).2) := by
  let v := widths d q (Fin.snoc w n)
  let hvw := fun l hl ↦ widths_snoc_le d q w n l hl
  have hvn : v (h + 1) = n + 1 := by
    change widths d q (Fin.snoc w n) (h + 1) = n + 1
    rw [hvw (h + 1) le_rfl]
    simp [widths]
  let e : Fin (n + 1) ≃ Fin (v (h + 1)) := finCongr hvn.symm
  have hae := network_succ_chain_hypotheses_ae (h + 1) (Nat.zero_lt_succ h) v hσ hβ
    (fun a ↦ inputForWidths d q (Fin.snoc w n) (X a))
  filter_upwards [hae] with θ hθ
  let η := prefixParametersLinear (h + 1) v θ
  let θs := splitParameters (h + 1) v θ
  have hpre (a : Fin N) (i : Fin (n + 1)) :
      initializedOutput d (n + 1) σ β X w (transportParameters hvw θs.1) (a, i) =
        network (h + 1) v σ β η (inputForWidths d q (Fin.snoc w n) (X a)) (e i) := by
    simpa only [η, prefixParametersLinear_eq_split] using network_transport_apply hvw σ β θs.1
      (inputForWidths d q (Fin.snoc w n) (X a)) (outputForWidths d (n + 1) w i)
  have hntk (a b : Fin N) (i j : Fin (n + 1)) :
      initializedNTK d (n + 1) σ β X w (transportParameters hvw θs.1) ((a, i), (b, j)) =
        finiteNTK (h + 1) v σ β η
          (inputForWidths d q (Fin.snoc w n) (X a))
          (inputForWidths d q (Fin.snoc w n) (X b)) (e i) (e j) := by
    simpa only [η, prefixParametersLinear_eq_split] using finiteNTK_transport_apply hvw σ β θs.1
      (inputForWidths d q (Fin.snoc w n) (X a))
      (inputForWidths d q (Fin.snoc w n) (X b))
      (outputForWidths d (n + 1) w i) (outputForWidths d (n + 1) w j)
  have hweight (k : Fin q) (i : Fin (n + 1)) :
      lastLayerWeights (n + 1) q (transportParameters (lastWidthEquality d q w n) θs.2)
        (k, i) =
      θ (parameterIndexSplit (h + 1) v
        (Sum.inr ⟨0, outputForWidths d q (Fin.snoc w n) k, some (e i)⟩)) := by
    have hw := transportParameters_weight (lastWidthEquality d q w n) θs.2 0
      (outputForWidths d q (Fin.snoc w n) k) (e i)
    simpa only [θs, splitParameters_snd, parameterIndexSplit] using hw
  ext ab
  have ht := finiteNTK_succ (h + 1) (Nat.zero_lt_succ h) v σ β θ
    (inputForWidths d q (Fin.snoc w n) (X ab.1.1))
    (inputForWidths d q (Fin.snoc w n) (X ab.2.1))
    (outputForWidths d q (Fin.snoc w n) ab.1.2)
    (outputForWidths d q (Fin.snoc w n) ab.2.2)
    (fun i ↦ (hθ ab.1.1 i).1) (fun i ↦ (hθ ab.2.1 i).1)
    (fun i ↦ (hθ ab.1.1 i).2) (fun i ↦ (hθ ab.2.1 i).2)
  dsimp -zetaDelta only at ht
  simp_rw [← e.sum_comp] at ht
  dsimp only [η] at hpre hntk
  simp_rw [← hpre] at ht
  simp_rw [← hntk] at ht
  simp_rw [← hweight] at ht
  rw [show (v (h + 1) : ℝ) = (n + 1 : ℕ) by exact_mod_cast hvn] at ht
  have houtputs : (outputForWidths d q (Fin.snoc w n) ab.1.2 =
      outputForWidths d q (Fin.snoc w n) ab.2.2) = (ab.1.2 = ab.2.2) := by
    apply propext
    simp only [outputForWidths, Fin.ext_iff]
  simp only [houtputs] at ht
  exact ht

end JGH

end

/- Bundled from Definitions/JGH/NTKSplitLaw.lean. -/
/-!
The pushforward-law form of the finite-width NTK recurrence in
Jacot--Gabriel--Hongler, arXiv:1806.07572v4, Appendix A.1, PDF p. 13.
This formal bridge combines the almost-everywhere chain rule with the exact
independent split of Gaussian parameters into the prefix and last affine layer.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal
namespace JGH

theorem measurable_upperNTK_prefix_state {h N : ℕ} (d n q : ℕ) {σ : ℝ → ℝ}
    {K : ℝ≥0} (hσ : LipschitzWith K σ) (β : ℝ) (X : Fin N → Input d)
    (w : Fin h → ℕ) :
    Measurable (fun z : Parameters (h + 1) (widths d n w) ×
        Parameters 1 (widths n q Fin.elim0) ↦
      upperNTK n q σ β
        ((initializedOutput d n σ β X w z.1, initializedNTK d n σ β X w z.1),
          lastLayerWeights n q z.2)) :=
  (measurable_upperNTK n q hσ.continuous β).comp
    (((measurable_initializedOutput d n hσ β X w).prodMk
      (measurable_initializedNTK d n σ β X w)).prodMap
        (continuous_lastLayerWeights n q).measurable)

theorem initializedNTKLaw_snoc_split {h N : ℕ} (d q : ℕ) {σ : ℝ → ℝ}
    {K : ℝ≥0} (hσ : LipschitzWith K σ) {β : ℝ} (hβ : 0 < β)
    (X : Fin N → Input d) (w : Fin h → ℕ) (n : ℕ) :
    initializedNTKLaw d q σ β X (Fin.snoc w n) =
      probabilityLaw
        ((initialization (h + 1) (widths d (n + 1) w)).prod
          (initialization 1 (widths (n + 1) q Fin.elim0)))
        (fun z ↦ upperNTK (n + 1) q σ β
          ((initializedOutput d (n + 1) σ β X w z.1,
            initializedNTK d (n + 1) σ β X w z.1),
            lastLayerWeights (n + 1) q z.2))
        (measurable_upperNTK_prefix_state d (n + 1) q hσ β X w) := by
  apply Subtype.ext
  dsimp only [initializedNTKLaw, probabilityLaw]
  rw [← (measurePreserving_splitWidthParameters d q w n).map_eq,
    Measure.map_map (measurable_upperNTK_prefix_state d (n + 1) q hσ β X w)
      (splitWidthParameters d q w n).measurable]
  exact Measure.map_congr (initializedNTK_snoc_split_ae d q hσ hβ X w n)

end JGH

end

/- Bundled from Solutions/Sol_JGH_NTKInitialization.lean. -/
noncomputable section
open MeasureTheory ProbabilityTheory Filter Matrix
open scoped BigOperators Topology ENNReal NNReal
namespace JGH

def prefixNTKState {h N : ℕ} (d n q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) (w : Fin h → ℕ)
    (z : Parameters (h + 1) (widths d n w) × Parameters 1 (widths n q Fin.elim0)) :
    UpperNTKState N n q :=
  ((initializedOutput d n σ β X w z.1, initializedNTK d n σ β X w z.1),
    lastLayerWeights n q z.2)

theorem measurable_prefixNTKState {h N : ℕ} (d n q : ℕ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) (β : ℝ) (X : Fin N → Input d) (w : Fin h → ℕ) :
    Measurable (prefixNTKState d n q σ β X w) :=
  ((measurable_initializedOutput d n hσ β X w).prodMk
    (measurable_initializedNTK d n σ β X w)).prodMap
    (continuous_lastLayerWeights n q).measurable

theorem prefixNTKState_tendstoInDistribution {h N : ℕ} (d n q : ℕ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) (β : ℝ) (X : Fin N → Input d)
    (hNTK : Tendsto (initializedNTKLaw (h := h) d n σ β X) (sequentialWidths h)
      (𝓝 (⟨Measure.dirac (deterministicNTKVector d n σ β h X), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (NTKEntryIndex N n))))) :
    TendstoInDistribution (prefixNTKState (h := h) d n q σ β X) (sequentialWidths h)
      (fun z : EuclideanSpace ℝ (Fin N × Fin n) × EuclideanSpace ℝ (Fin q × Fin n) ↦
        ((z.1, deterministicNTKVector d n σ β h X), z.2))
      (fun w ↦ (initialization (h + 1) (widths d n w)).prod
        (initialization 1 (widths n q Fin.elim0)))
      ((outputGaussian d n σ β h X).prod
        (multivariateGaussian 0 (1 : Matrix (Fin q × Fin n) (Fin q × Fin n) ℝ))) := by
  let c := deterministicNTKVector d n σ β h X
  have hclose := fun δ (hδ : 0 < δ) ↦
    tendsto_probability_dist_ge_of_law_tendsto_dirac
      (fun w ↦ initialization (h + 1) (widths d n w))
      (initializedNTK d n σ β X) (measurable_initializedNTK d n σ β X) c hNTK hδ
  have hj := tendstoInDistribution_prod_const
    (fun w ↦ initialization (h + 1) (widths d n w)) (outputGaussian d n σ β h X)
    (initializedOutput d n σ β X) (initializedNTK d n σ β X) id c
    (measurable_initializedOutput d n hσ β X) (measurable_initializedNTK d n σ β X)
    (gaussianInitialization_all d n hσ β h X) hclose
  let νs (w : Fin h → ℕ) : ProbabilityMeasure
      (EuclideanSpace ℝ (Fin N × Fin n) × EuclideanSpace ℝ (NTKEntryIndex N n)) :=
    ⟨(initialization (h + 1) (widths d n w)).map
      (fun θ ↦ (initializedOutput d n σ β X w θ, initializedNTK d n σ β X w θ)),
      Measure.isProbabilityMeasure_map (hj.forall_aemeasurable w)⟩
  let ν : ProbabilityMeasure
      (EuclideanSpace ℝ (Fin N × Fin n) × EuclideanSpace ℝ (NTKEntryIndex N n)) :=
    ⟨(outputGaussian d n σ β h X).map (fun z ↦ (z, c)),
      Measure.isProbabilityMeasure_map hj.aemeasurable_limit⟩
  let ρ : ProbabilityMeasure (EuclideanSpace ℝ (Fin q × Fin n)) :=
    ⟨multivariateGaussian 0 (1 : Matrix (Fin q × Fin n) (Fin q × Fin n) ℝ), inferInstance⟩
  have hp : Tendsto (fun w ↦ (νs w).prod ρ) (sequentialWidths h) (𝓝 (ν.prod ρ)) :=
    (ProbabilityMeasure.continuous_prod.tendsto (ν, ρ)).comp
      (hj.tendsto.prodMk_nhds tendsto_const_nhds)
  refine ⟨fun w ↦ (measurable_prefixNTKState d n q hσ β X w).aemeasurable,
    (by fun_prop), ?_⟩
  convert hp using 1
  · ext w : 1
    apply Subtype.ext
    dsimp [νs, ρ]
    rw [← map_lastLayerWeights n q, Measure.map_prod_map _ _
      ((measurable_initializedOutput d n hσ β X w).prodMk
        (measurable_initializedNTK d n σ β X w)) (continuous_lastLayerWeights n q).measurable]
    rfl
  · congr 1
    apply Subtype.ext
    dsimp [ν, ρ]
    simpa only [Measure.map_id] using (Measure.map_prod_map
      (outputGaussian d n σ β h X)
      (multivariateGaussian 0 (1 : Matrix (Fin q × Fin n) (Fin q × Fin n) ℝ))
      (show Measurable (fun z : EuclideanSpace ℝ (Fin N × Fin n) ↦ (z, c)) by fun_prop)
      (show Measurable (id : EuclideanSpace ℝ (Fin q × Fin n) → _) from measurable_id)).symm

theorem upperNTK_inner_tendsto {h N : ℕ} (d n q : ℕ)
    {σ : ℝ → ℝ} {K : ℝ≥0} (hσ : LipschitzWith K σ) {β : ℝ} (hβ : 0 < β)
    (X : Fin N → Input d)
    (hNTK : Tendsto (initializedNTKLaw (h := h) d n σ β X) (sequentialWidths h)
      (𝓝 (⟨Measure.dirac (deterministicNTKVector d n σ β h X), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (NTKEntryIndex N n))))) :
    Tendsto (fun w ↦ probabilityLaw
      ((initialization (h + 1) (widths d n w)).prod
        (initialization 1 (widths n q Fin.elim0)))
      (fun z ↦ upperNTK n q σ β (prefixNTKState d n q σ β X w z))
      ((measurable_upperNTK n q hσ.continuous β).comp
        (measurable_prefixNTKState d n q hσ β X w)))
      (sequentialWidths h) (𝓝 (limitingUpperNTKLaw d n q σ hσ.continuous β h X)) := by
  have hj := prefixNTKState_tendstoInDistribution d n q hσ β X hNTK
  have haug := tendstoInDistribution_augmented_derivative_of_density_bound
    _ _ _ _ hj (upperNTKProjection n q) (biasDensityBound β) (fun w a ↦ ?_) hσ
  · have hm := haug.continuous_comp (continuous_upperNTKAugmented n q hσ.continuous β)
    exact hm.tendsto
  · exact scalar_density_bound_adjoin_prod
      (initialization (h + 1) (widths d n w)) (initialization 1 (widths n q Fin.elim0))
      (initializedOutput d n σ β X w) (initializedNTK d n σ β X w)
      (lastLayerWeights n q) (fun z : EuclideanSpace ℝ (Fin N × Fin n) ↦ z a)
      ((by fun_prop : Measurable (fun z : EuclideanSpace ℝ (Fin N × Fin n) ↦ z a)).comp
        (measurable_initializedOutput d n hσ β X w)) (biasDensityBound β)
      (initializedOutput_scalar_density_bound d n hσ hβ X w a)

theorem initializedNTKLaw_zero {N : ℕ} (d q : ℕ) (σ : ℝ → ℝ) (β : ℝ)
    (X : Fin N → Input d) (w : Fin 0 → ℕ) :
    initializedNTKLaw d q σ β X w =
      (⟨Measure.dirac (deterministicNTKVector d q σ β 0 X), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (NTKEntryIndex N q))) := by
  apply Subtype.ext
  change (initialization 1 (widths d q w)).map (initializedNTK d q σ β X w) = _
  have he : initializedNTK d q σ β X w = fun _ ↦ deterministicNTKVector d q σ β 0 X :=
    funext (initializedNTK_zero d q σ β X w)
  simp only [he, Measure.map_const, measure_univ, one_smul]

theorem ntkInitialization_law {N : ℕ} (d q : ℕ) {σ : ℝ → ℝ} {K : ℝ≥0}
    (hσ : LipschitzWith K σ) {β : ℝ} (hβ : 0 < β) (h : ℕ) (X : Fin N → Input d) :
    Tendsto (initializedNTKLaw (h := h) d q σ β X) (sequentialWidths h)
      (𝓝 (⟨Measure.dirac (deterministicNTKVector d q σ β h X), inferInstance⟩ :
        ProbabilityMeasure (EuclideanSpace ℝ (NTKEntryIndex N q)))) := by
  induction h generalizing q with
  | zero =>
      rw [funext (initializedNTKLaw_zero d q σ β X)]
      exact tendsto_const_nhds
  | succ h ih =>
      apply tendsto_sequentialWidths_succ
        (g := fun n ↦ limitingUpperNTKLaw d (n + 1) q σ hσ.continuous β h X)
      · intro n
        simpa only [initializedNTKLaw_snoc_split d q hσ hβ X, prefixNTKState] using
          upperNTK_inner_tendsto d (n + 1) q hσ hβ X (ih (n + 1))
      · exact limitingUpperNTKLaw_tendsto d q hσ β h X

end JGH

theorem solution :
  ∀ (d q : ℕ), 0 < d → 0 < q →
    ∀ (σ : ℝ → ℝ) (K : ℝ≥0), LipschitzWith K σ →
      ∀ (β : ℝ), 0 < β → ∀ (h N : ℕ) (X : Fin N → JGH.Input d)
        (ε : ℝ), 0 < ε →
        Tendsto (JGH.ntkBadProbability (h := h) d q σ β X ε)
          (JGH.sequentialWidths h) (𝓝 0) := by
  intro d q _ _ σ K hσ β hβ h N X ε hε
  exact JGH.ntkBadProbability_tendsto_of_law_tendsto_dirac d q σ β X
    (JGH.ntkInitialization_law d q hσ hβ h X) hε

end

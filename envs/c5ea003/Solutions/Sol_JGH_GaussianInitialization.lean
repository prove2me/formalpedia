-- Prove2me | solution 1 for JGH.GaussianInitialization
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-26T03:28:54.453015+00:00
-- url     : https://prove2.me/submissions/5a83b97f-9a7c-4a14-b6b1-eca65cb14a4c

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

/- Bundled from Solutions/Sol_JGH_GaussianInitialization.lean. -/
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

theorem solution :
  ∀ (d q : ℕ), 0 < d → 0 < q →
    ∀ (σ : ℝ → ℝ) (K : ℝ≥0), LipschitzWith K σ →
      ∀ (β : ℝ), 0 < β → ∀ (h N : ℕ) (X : Fin N → JGH.Input d),
        TendstoInDistribution (JGH.initializedOutput (h := h) d q σ β X)
          (JGH.sequentialWidths h) id (fun w ↦ JGH.initialization (h + 1) (JGH.widths d q w))
          (JGH.outputGaussian d q σ β h X) := by
  intro d q _ _ σ K hσ β _ h N X
  exact JGH.gaussianInitialization_all d q hσ β h X

end

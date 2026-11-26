-- Prove2me | solution 1 for ReweightedNPMLE.gaussian_generic_evaluation_independence
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:15:14.419471+00:00
-- url     : https://prove2.me/submissions/d90a1d58-7b1a-4750-909e-0d362720cc39

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Implicit
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Card
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Order.Filter.Finite
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Probability.Moments.ComplexMGF
import Mathlib.Tactic
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.LocallyClosed
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.CoveringNumbers
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_DirichletIndependence
import Definitions.Def_ReweightedNPMLE_ExtremeSupport
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_FittedEnvelope
import Definitions.Def_ReweightedNPMLE_FittedGeometry
import Definitions.Def_ReweightedNPMLE_FittedHessian
import Definitions.Def_ReweightedNPMLE_FittedLocalization
import Definitions.Def_ReweightedNPMLE_FittedRegularity
import Definitions.Def_ReweightedNPMLE_FullEffectiveDimension
import Definitions.Def_ReweightedNPMLE_GammaEffectiveEvent
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianGenericity
import Definitions.Def_ReweightedNPMLE_GaussianIncidence
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_GaussianStructural
import Definitions.Def_ReweightedNPMLE_GaussianWidth
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_IncidenceJacobian
import Definitions.Def_ReweightedNPMLE_MeasureExtremeSupport
import Definitions.Def_ReweightedNPMLE_MeasureFiberPerturbation
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_SupportSensitivity
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_analyticAt_gaussianDependenceFamily_joint
import Theorems.Thm_ReweightedNPMLE_analyticAt_gaussianKernel_joint
import Theorems.Thm_ReweightedNPMLE_exists_regular_iterated_derivative_of_analytic_zero
import Theorems.Thm_ReweightedNPMLE_finiteGaussianMixture_coefficients_zero_of_eq_zero
import Theorems.Thm_ReweightedNPMLE_gaussian_evaluation_dependence_has_normalized_chart
import Theorems.Thm_ReweightedNPMLE_measure_projection_regular_zero_locus_eq_zero

-- Inline helpers preserved from ReweightedNPMLE.GaussianIncidence.
section
/-!
# Nontrivial Gaussian families for the generic incidence argument

Distinct Gaussian translates are linearly independent as functions on the
whole observation space. This is proved using Gaussian mixture identifiability
and a positive finite-probability perturbation, so no choice of a separating
direction or Vandermonde derivative calculation is required.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE





/-- Nonzero normalized coefficients cannot define an identically zero family,
uniformly over every distinct location list. -/
theorem finiteGaussianMixture_not_identically_zero {d k : ℕ}
    (θ : Fin k → Point d) (hθ : Function.Injective θ) (c : Fin k → ℝ)
    (hc : ∃ j, c j ≠ 0) : ∃ x, finiteGaussianMixture c θ x ≠ 0 := by
  by_contra hn
  have hzero : ∀ x, finiteGaussianMixture c θ x = 0 := by simpa using hn
  obtain ⟨j, hj⟩ := hc
  exact hj (finiteGaussianMixture_coefficients_zero_of_eq_zero θ hθ c hzero j)





theorem analyticAt_finiteGaussianMixture_parameter {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {d k : ℕ}
    (θ : Fin k → E → Point d) (c : Fin k → E → ℝ) (y : E → Point d) (e : E)
    (hθ : ∀ j, AnalyticAt ℝ (θ j) e) (hc : ∀ j, AnalyticAt ℝ (c j) e)
    (hy : AnalyticAt ℝ y e) :
    AnalyticAt ℝ (fun a ↦ finiteGaussianMixture (fun j ↦ c j a) (fun j ↦ θ j a) (y a)) e := by
  unfold finiteGaussianMixture
  apply Finset.analyticAt_fun_sum
  intro j _
  exact (hc j).mul ((analyticAt_gaussianKernel_joint (y e, θ j e)).comp
    (f := fun a ↦ (y a, θ j a)) (hy.prod (hθ j)))

theorem analyticOnNhd_finiteGaussianMixture {d k : ℕ}
    (θ : Fin k → Point d) (c : Fin k → ℝ) :
    AnalyticOnNhd ℝ (finiteGaussianMixture c θ) univ := by
  intro x _
  exact analyticAt_finiteGaussianMixture_parameter (fun j _ ↦ θ j) (fun j _ ↦ c j) id x
    (fun _ ↦ analyticAt_const) (fun _ ↦ analyticAt_const) analyticAt_id











theorem finrank_gaussianDependenceParameter {d k : ℕ} (j₀ : Fin k) :
    Module.finrank ℝ (GaussianDependenceParameter d k j₀) = k * d + (k - 1) := by
  have hcard : Fintype.card {j : Fin k // j ≠ j₀} = k - 1 := by
    simpa using Fintype.card_subtype_compl (fun j : Fin k ↦ j = j₀)
  simp [GaussianDependenceParameter, Module.finrank_prod, Module.finrank_pi_fintype,
    hcard]

theorem finrank_gaussianDependenceParameter_lt {d k n : ℕ} (j₀ : Fin k)
    (hkn : k * (d + 1) ≤ n) :
    Module.finrank ℝ (GaussianDependenceParameter d k j₀) < n := by
  rw [finrank_gaussianDependenceParameter]
  have hk : 0 < k := Fin.pos j₀
  rw [Nat.mul_add, Nat.mul_one] at hkn
  omega





theorem gaussianDependenceFamily_nontrivial {d k : ℕ} (j₀ : Fin k)
    (η : GaussianDependenceParameter d k j₀) (hη : η ∈ gaussianDependenceDomain j₀) :
    ∃ y, gaussianDependenceFamily j₀ η y ≠ 0 := by
  apply finiteGaussianMixture_not_identically_zero η.1 hη
  refine ⟨j₀, ?_⟩
  simp [normalizedGaussianCoefficients]

theorem gaussianDependenceFamily_regular_derivative_at_zero {d k : ℕ} (j₀ : Fin k)
    (η : GaussianDependenceParameter d k j₀) (hη : η ∈ gaussianDependenceDomain j₀)
    (x : Point d) (hx : gaussianDependenceFamily j₀ η x = 0) :
    ∃ (m : ℕ) (ℓ : Fin d) (σ : Fin m → Fin d),
      iteratedFDeriv ℝ m (gaussianDependenceFamily j₀ η) x
        (fun i ↦ (EuclideanSpace.basisFun (Fin d) ℝ) (σ i)) = 0 ∧
      fderiv ℝ (fun y ↦ iteratedFDeriv ℝ m (gaussianDependenceFamily j₀ η) y
        (fun i ↦ (EuclideanSpace.basisFun (Fin d) ℝ) (σ i))) x
          ((EuclideanSpace.basisFun (Fin d) ℝ) ℓ) ≠ 0 := by
  exact exists_regular_iterated_derivative_of_analytic_zero
    (EuclideanSpace.basisFun (Fin d) ℝ).toBasis _
    (analyticOnNhd_finiteGaussianMixture η.1 (normalizedGaussianCoefficients j₀ η.2))
    (gaussianDependenceFamily_nontrivial j₀ η hη) x hx



end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.IncidenceSmoothness.
section
/-!
# Joint smoothness of observation derivatives

Differentiating only in the observation variable preserves joint smoothness
in parameters and observations. Evaluation of the resulting multilinear
derivative on a fixed basis word is also jointly smooth.
-/

open Set Filter
open scoped BigOperators Topology

namespace ReweightedNPMLE

theorem contDiff_iteratedFDeriv_with_parameter
    {E Y Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : E → Y → Z) (hf : ContDiff ℝ ⊤ (Function.uncurry F)) (m : ℕ) :
    ContDiff ℝ ⊤ (fun p : E × Y ↦ iteratedFDeriv ℝ m (F p.1) p.2) := by
  induction m with
  | zero =>
    exact hf.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ Y Z).symm : Z →L[ℝ] Y [×0]→L[ℝ] Z)
  | succ m ih =>
    have hg : ContDiff ℝ ⊤ (Function.uncurry
        (fun p : E × Y ↦ fun y : Y ↦ iteratedFDeriv ℝ m (F p.1) y)) :=
      ih.comp (show ContDiff ℝ ⊤ (fun q : (E × Y) × Y ↦ (q.1.1, q.2)) by fun_prop)
    have hd : ContDiff ℝ ⊤ (fun p : E × Y ↦
        fderiv ℝ (fun y ↦ iteratedFDeriv ℝ m (F p.1) y) p.2) :=
      hg.fderiv contDiff_snd (by simp)
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) ↦ Y) Z).symm :
        (Y →L[ℝ] Y [×m]→L[ℝ] Z) →L[ℝ] Y [×(m + 1)]→L[ℝ] Z)

theorem contDiff_iteratedFDeriv_word_with_parameter
    {E Y Z : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (F : E → Y → Z) (hf : ContDiff ℝ ⊤ (Function.uncurry F))
    (m : ℕ) (u : Fin m → Y) :
    ContDiff ℝ ⊤ (fun p : E × Y ↦ iteratedFDeriv ℝ m (F p.1) p.2 u) :=
  (contDiff_iteratedFDeriv_with_parameter F hf m).continuousLinearMap_comp
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin m ↦ Y) Z u)

end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.IncidenceJacobian.
section
/-!
# Full row rank of separated incidence equations

Each scalar equation depends on the common parameter and one observation row.
Nonzero selected observation derivatives give an explicit right inverse for
the full incidence derivative, without constraining the parameter derivative.
-/

open Set Filter
open scoped BigOperators Topology

namespace ReweightedNPMLE







theorem hasFDerivAt_incidenceEquations {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
    (H : Fin n → E → Y → ℝ) (p : E × (Fin n → Y))
    (hH : ∀ i, DifferentiableAt ℝ (Function.uncurry (H i)) (p.1, p.2 i)) :
    HasFDerivAt (incidenceEquations H) (incidenceDerivative H p) p := by
  apply hasFDerivAt_pi.mpr
  intro i
  exact (hH i).hasFDerivAt.comp p (incidenceRowProjection i).hasFDerivAt

theorem contDiff_incidenceEquations_of_joint {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
    (H : Fin n → E → Y → ℝ)
    (hH : ∀ i, ContDiff ℝ ⊤ (Function.uncurry (H i))) :
    ContDiff ℝ ⊤ (incidenceEquations H) := by
  apply contDiff_pi.mpr
  intro i
  exact (hH i).comp (incidenceRowProjection i).contDiff

theorem fderiv_uncurry_observation_apply {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (H : E → Y → ℝ) (η : E) (y u : Y)
    (hH : DifferentiableAt ℝ (Function.uncurry H) (η, y)) :
    fderiv ℝ (Function.uncurry H) (η, y) (0, u) = fderiv ℝ (H η) y u := by
  have hp := hH.hasFDerivAt.comp y
    ((hasFDerivAt_const η y).prodMk (hasFDerivAt_id y))
  have hh := congrArg (fun L : Y →L[ℝ] ℝ ↦ L u) hp.fderiv
  simpa using hh.symm

theorem incidenceDerivative_surjective_of_observation_derivatives {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
    (H : Fin n → E → Y → ℝ) (p : E × (Fin n → Y))
    (hH : ∀ i, DifferentiableAt ℝ (Function.uncurry (H i)) (p.1, p.2 i))
    (u : Fin n → Y) (hu : ∀ i, fderiv ℝ (H i p.1) (p.2 i) (u i) ≠ 0) :
    Function.Surjective (incidenceDerivative H p) := by
  let δ : Fin n → ℝ := fun i ↦ fderiv ℝ (Function.uncurry (H i)) (p.1, p.2 i) (0, u i)
  have hδ : ∀ i, δ i ≠ 0 := by
    intro i
    dsimp only [δ]
    rw [fderiv_uncurry_observation_apply (H i) p.1 (p.2 i) (u i) (hH i)]
    exact hu i
  intro z
  refine ⟨(0, fun i ↦ (z i / δ i) • u i), ?_⟩
  funext i
  change fderiv ℝ (Function.uncurry (H i)) (p.1, p.2 i)
    (0, (z i / δ i) • u i) = z i
  have heq : ((0 : E), (z i / δ i) • u i) = (z i / δ i) • ((0 : E), u i) := by simp
  rw [heq, map_smul]
  change (z i / δ i) * δ i = z i
  exact div_mul_cancel₀ _ (hδ i)

theorem fderiv_incidenceEquations_surjective {E Y : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {n : ℕ}
    (H : Fin n → E → Y → ℝ) (p : E × (Fin n → Y))
    (hH : ∀ i, DifferentiableAt ℝ (Function.uncurry (H i)) (p.1, p.2 i))
    (u : Fin n → Y) (hu : ∀ i, fderiv ℝ (H i p.1) (p.2 i) (u i) ≠ 0) :
    Function.Surjective (fderiv ℝ (incidenceEquations H) p) := by
  rw [(hasFDerivAt_incidenceEquations H p hH).fderiv]
  exact incidenceDerivative_surjective_of_observation_derivatives H p hH u hu

end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianGenericity.
section
/-!
# Simultaneous Gaussian evaluation independence

Normalized Gaussian dependence charts are covered by countably many regular
derivative-equation loci. Their nuisance dimension is below the number of
sample equations, so the implicit-function null-projection theorem excludes
all data-dependent location dependences on one Borel conull data set.
-/

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE





theorem contDiff_gaussianObservationDerivativeFamily_joint {d k : ℕ} (j₀ : Fin k)
    (ω : ObservationDerivativeIndex d) :
    ContDiff ℝ ⊤ (Function.uncurry (gaussianObservationDerivativeFamily j₀ ω)) := by
  have hf : AnalyticOnNhd ℝ (Function.uncurry (gaussianDependenceFamily (d := d) j₀)) univ :=
    fun p _ ↦ analyticAt_gaussianDependenceFamily_joint j₀ p
  exact contDiff_iteratedFDeriv_word_with_parameter _ hf.contDiff ω.1
    (fun i ↦ (EuclideanSpace.basisFun (Fin d) ℝ) (ω.2 i))



theorem gaussianIncidence_has_regular_derivative_equations {d k n : ℕ} (j₀ : Fin k)
    (p : GaussianDependenceParameter d k j₀ × (Fin n → Point d))
    (hp : p ∈ gaussianIncidenceSet j₀) :
    ∃ ω : Fin n → ObservationDerivativeIndex d,
      incidenceEquations (fun i ↦ gaussianObservationDerivativeFamily j₀ (ω i)) p = 0 ∧
      Function.Surjective (fderiv ℝ
        (incidenceEquations (fun i ↦ gaussianObservationDerivativeFamily j₀ (ω i))) p) := by
  have hregular := fun i ↦ gaussianDependenceFamily_regular_derivative_at_zero j₀ p.1 hp.1
    (p.2 i) (hp.2 i)
  choose m ℓ σ hzero hnonzero using hregular
  let ω : Fin n → ObservationDerivativeIndex d := fun i ↦ ⟨m i, σ i⟩
  refine ⟨ω, funext hzero, ?_⟩
  exact fderiv_incidenceEquations_surjective _ p
    (fun i ↦ (contDiff_gaussianObservationDerivativeFamily_joint j₀ (ω i)).differentiable
      (by simp) |>.differentiableAt) (fun i ↦ (EuclideanSpace.basisFun (Fin d) ℝ) (ℓ i)) hnonzero

theorem volume_projection_gaussianIncidenceSet_eq_zero {d k n : ℕ} (j₀ : Fin k)
    (hkn : k * (d + 1) ≤ n) :
    volume ((ContinuousLinearMap.snd ℝ (GaussianDependenceParameter d k j₀)
      (Fin n → Point d)) '' gaussianIncidenceSet (n := n) j₀) = 0 := by
  let π := ContinuousLinearMap.snd ℝ (GaussianDependenceParameter d k j₀) (Fin n → Point d)
  let g := fun ω : Fin n → ObservationDerivativeIndex d ↦
    incidenceEquations (fun i ↦ gaussianObservationDerivativeFamily j₀ (ω i))
  let R := fun ω : Fin n → ObservationDerivativeIndex d ↦
    {p | g ω p = 0 ∧ Function.Surjective (fderiv ℝ (g ω) p)}
  have hdim : Module.finrank ℝ
      (GaussianDependenceParameter d k j₀ × (Fin n → Point d)) <
        Module.finrank ℝ (Fin n → Point d) + Module.finrank ℝ (Fin n → ℝ) := by
    have hh := finrank_gaussianDependenceParameter_lt j₀ hkn
    rw [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
    omega
  have hnull : ∀ ω : Fin n → ObservationDerivativeIndex d, volume (π '' R ω) = 0 := by
    intro ω
    exact measure_projection_regular_zero_locus_eq_zero volume π (g ω)
      ((contDiff_incidenceEquations_of_joint _
        (fun i ↦ contDiff_gaussianObservationDerivativeFamily_joint j₀ (ω i))).of_le le_top) hdim
  have hunion : volume (⋃ ω : Fin n → ObservationDerivativeIndex d, π '' R ω) = 0 :=
    measure_iUnion_null_iff.mpr hnull
  apply measure_mono_null _ hunion
  rintro x ⟨p, hp, rfl⟩
  obtain ⟨ω, hzero, hsurj⟩ := gaussianIncidence_has_regular_derivative_equations j₀ p hp
  exact mem_iUnion.mpr ⟨ω, ⟨p, ⟨hzero, hsurj⟩, rfl⟩⟩



theorem volume_gaussianBadData_eq_zero (n d : ℕ) : volume (gaussianBadData n d) = 0 := by
  unfold gaussianBadData
  apply measure_iUnion_null_iff.mpr
  intro k
  apply measure_iUnion_null_iff.mpr
  intro j₀
  split_ifs with hkn
  · exact volume_projection_gaussianIncidenceSet_eq_zero j₀ hkn
  · exact measure_empty







end ReweightedNPMLE
end

/-!
# Simultaneous Gaussian evaluation independence

Normalized Gaussian dependence charts are covered by countably many regular
derivative-equation loci. Their nuisance dimension is below the number of
sample equations, so the implicit-function null-projection theorem excludes
all data-dependent location dependences on one Borel conull data set.
-/

open Set Filter MeasureTheory MeasureTheory.Measure
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Proposition: one Borel conull data set works simultaneously for every
distinct location list with `k(d+1) <= n`. Locations may depend on the data. -/
theorem solution (n d : ℕ) :
    ∃ X : Set (Fin n → Point d), MeasurableSet X ∧ volume Xᶜ = 0 ∧
      ∀ x ∈ X, ∀ k : ℕ, k * (d + 1) ≤ n → ∀ θ : Fin k → Point d,
        Function.Injective θ →
          LinearIndependent ℝ (fun j i ↦ gaussianKernel d (x i) (θ j)) := by
  let N := toMeasurable volume (gaussianBadData n d)
  refine ⟨Nᶜ, (measurableSet_toMeasurable volume _).compl, ?_, ?_⟩
  · rw [compl_compl]
    exact (measure_toMeasurable (μ := volume) (gaussianBadData n d)).trans
      (volume_gaussianBadData_eq_zero n d)
  · intro x hx k hk θ hθ
    by_contra hdep
    obtain ⟨j₀, η, hη, hzero⟩ := gaussian_evaluation_dependence_has_normalized_chart θ hθ x hdep
    have hbad : x ∈ gaussianBadData n d := by
      unfold gaussianBadData
      refine mem_iUnion.mpr ⟨k, mem_iUnion.mpr ⟨j₀, ?_⟩⟩
      rw [if_pos hk]
      exact ⟨(η, x), ⟨hη, hzero⟩, rfl⟩
    exact hx (subset_toMeasurable volume _ hbad)

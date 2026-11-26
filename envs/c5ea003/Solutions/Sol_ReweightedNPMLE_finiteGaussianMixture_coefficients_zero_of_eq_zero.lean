-- Prove2me | solution 1 for ReweightedNPMLE.finiteGaussianMixture_coefficients_zero_of_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:13:26.522358+00:00
-- url     : https://prove2.me/submissions/d9ff7ba5-ca51-406a-a5c1-8fb0ac118fbe

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Multilinear.Basis
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Independence.CharacteristicFunction
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_FiniteOptimizerFiber
import Definitions.Def_ReweightedNPMLE_FittedContact
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianIncidence
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_ProbabilityFiberGeometry
import Definitions.Def_ReweightedNPMLE_ProbabilityOptimizerFiber
import Definitions.Def_ReweightedNPMLE_Weights
import Theorems.Thm_ReweightedNPMLE_gaussianLocationMixtureLaw_injective

-- Inline helpers preserved from ReweightedNPMLE.FiniteProbabilityExtreme.
section
/-!
# Independent finite mixing laws are full-fiber extreme points

Finite-support representation and uniqueness are proved for arbitrary
probability measures concentrated on that finite support. Consequently,
an independent finite mixing law is extreme against decompositions into
arbitrary probability measures, not only against finite coefficient vectors.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

namespace ReweightedNPMLE







theorem finiteProbabilityMeasure_singleton_mass {Θ : Type*}
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] {m : ℕ}
    (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (p : Fin m → ℝ) (hp : p ∈ finiteSimplex m) (j : Fin m) :
    (finiteProbabilityMeasure θ p hp : Measure Θ) {θ j} = ENNReal.ofReal (p j) := by
  classical
  change (∑ k, ENNReal.ofReal (p k) • Measure.dirac (θ k)) {θ j} = _
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    have hneq : θ k ≠ θ j := fun hh ↦ hkj (hθ hh)
    simp [hneq]
  · simp

theorem finiteProbabilityMeasure_coefficients_injective {Θ : Type*}
    [MeasurableSpace Θ] [MeasurableSingletonClass Θ] {m : ℕ}
    (θ : Fin m → Θ) (hθ : Function.Injective θ)
    (p q : Fin m → ℝ) (hp : p ∈ finiteSimplex m) (hq : q ∈ finiteSimplex m)
    (heq : finiteProbabilityMeasure θ p hp = finiteProbabilityMeasure θ q hq) : p = q := by
  funext j
  have hh := congrArg (fun μ : ProbabilityMeasure Θ ↦ (μ : Measure Θ) {θ j}) heq
  dsimp only at hh
  rw [finiteProbabilityMeasure_singleton_mass θ hθ p hp,
    finiteProbabilityMeasure_singleton_mass θ hθ q hq] at hh
  have hr := congrArg ENNReal.toReal hh
  simpa only [ENNReal.toReal_ofReal (hp.1 j), ENNReal.toReal_ofReal (hq.1 j)] using hr

















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.Gaussian.
section
/-!
# Gaussian location-mixture algebra

The manuscript factors a Gaussian translate into a common density and an exponential
score.  This file formalizes that identity and the uniform score bounds used in both the
effective-dimension and finite-net arguments.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE





































/-- Every translated Gaussian kernel is integrable. -/
theorem gaussianKernel_integrable (d : ℕ) (θ : Point d) :
    Integrable (fun x ↦ gaussianKernel d x θ) := by
  change Integrable (fun x ↦ gaussianDensity d (x - θ))
  exact (gaussianDensity_integrable d).comp_sub_right θ

/-- Every translated Gaussian kernel integrates to one. -/
theorem integral_gaussianKernel (d : ℕ) (θ : Point d) :
    ∫ x : Point d, gaussianKernel d x θ = 1 := by
  change (∫ x : Point d, gaussianDensity d (x - θ)) = 1
  rw [integral_sub_right_eq_self, integral_gaussianDensity]



/-- The integral of a finite Gaussian mixture is the sum of its weights. -/
theorem integral_finiteGaussianMixture {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) :
    ∫ x, finiteGaussianMixture w θ x = ∑ i, w i := by
  unfold finiteGaussianMixture
  rw [integral_finsetSum Finset.univ]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul, integral_gaussianKernel, mul_one]
  · intro i _
    exact (gaussianKernel_integrable d (θ i)).const_mul (w i)



















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianIdentifiability.
section
/-!
# Identifiability of Gaussian location mixtures

Convolution with a standard Gaussian is injective on probability measures:
its characteristic function is nowhere zero.  Combined with the generative-
law/density identity, this proves identifiability of the mixing law from the
mixture density.
-/

open MeasureTheory ProbabilityTheory Filter Topology BoundedContinuousFunction

namespace ReweightedNPMLE







/-- Two probability mixing laws with almost-everywhere equal Gaussian
location-mixture densities are equal. -/
theorem gaussianMixture_identifiable_of_ae_eq
    {d : ℕ} (μ ν : Measure (Point d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : gaussianMixture μ id =ᵐ[volume] gaussianMixture ν id) : μ = ν := by
  apply gaussianLocationMixtureLaw_injective μ ν
  rw [gaussianLocationMixtureLaw_eq_withDensity_gaussianMixture
      μ id measurable_id,
    gaussianLocationMixtureLaw_eq_withDensity_gaussianMixture
      ν id measurable_id]
  apply withDensity_congr_ae
  filter_upwards [h] with x hx
  rw [hx]















end ReweightedNPMLE
end

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

theorem gaussianMixture_finiteProbabilityMeasure {d k : ℕ}
    (θ : Fin k → Point d) (p : Fin k → ℝ) (hp : p ∈ finiteSimplex k) :
    gaussianMixture (finiteProbabilityMeasure θ p hp : Measure (Point d)) id =
      finiteGaussianMixture p θ := by
  funext x
  change (∫ a, gaussianKernel d x a ∂(∑ j, ENNReal.ofReal (p j) • Measure.dirac (θ j))) = _
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal (hp.1 _),
      finiteGaussianMixture, smul_eq_mul]
  · intro j _
    exact (integrable_dirac (by simp)).smul_measure ENNReal.ofReal_ne_top





































end ReweightedNPMLE
end

/-!
# Nontrivial Gaussian families for the generic incidence argument

Distinct Gaussian translates are linearly independent as functions on the
whole observation space. This is proved using Gaussian mixture identifiability
and a positive finite-probability perturbation, so no choice of a separating
direction or Vandermonde derivative calculation is required.
-/

open Set MeasureTheory Filter
open scoped BigOperators Topology NNReal ENNReal

open ReweightedNPMLE
open ReweightedNPMLE in
theorem solution {d k : ℕ}
    (θ : Fin k → Point d) (hθ : Function.Injective θ) (c : Fin k → ℝ)
    (hzero : ∀ x, finiteGaussianMixture c θ x = 0) : ∀ j, c j = 0 := by
  classical
  by_cases hk : k = 0
  · subst k
    intro j
    exact Fin.elim0 j
  have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hk)
  have hsum : ∑ j, c j = 0 := by
    rw [← integral_finiteGaussianMixture c θ]
    simp only [hzero, integral_zero]
  let b : ℝ := 1 / (k : ℝ)
  let M : ℝ := ∑ j, |c j|
  let t : ℝ := b / (2 * (1 + M))
  let p : Fin k → ℝ := fun _ ↦ b
  let q : Fin k → ℝ := fun j ↦ b + t * c j
  have hb : 0 < b := by dsimp [b]; positivity
  have hM : 0 ≤ M := Finset.sum_nonneg (fun j _ ↦ abs_nonneg (c j))
  have ht : 0 < t := by dsimp [t]; positivity
  have htEq : t * (1 + M) = b / 2 := by
    dsimp [t]
    field_simp
  have hbound : ∀ j, |c j| ≤ M := fun j ↦
    Finset.single_le_sum (fun l _ ↦ abs_nonneg (c l)) (Finset.mem_univ j)
  have hp : p ∈ finiteSimplex k := by
    refine ⟨fun _ ↦ hb.le, ?_⟩
    simp only [p, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, b]
    field_simp
  have hq : q ∈ finiteSimplex k := by
    constructor
    · intro j
      have hc : -M ≤ c j := by linarith [(abs_le.mp (hbound j)).1]
      have hh := mul_le_mul_of_nonneg_left hc ht.le
      dsimp [q]
      nlinarith
    · simp only [q, Finset.sum_add_distrib, ← Finset.mul_sum, hsum, mul_zero, add_zero]
      exact hp.2
  have hdensity : finiteGaussianMixture q θ = finiteGaussianMixture p θ := by
    funext x
    have heq : finiteGaussianMixture q θ x =
        finiteGaussianMixture p θ x + t * finiteGaussianMixture c θ x := by
      simp only [finiteGaussianMixture, q, p, add_mul, Finset.sum_add_distrib,
        Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [heq, hzero, mul_zero, add_zero]
  have hmeas : (finiteProbabilityMeasure θ q hq : Measure (Point d)) =
      (finiteProbabilityMeasure θ p hp : Measure (Point d)) := by
    apply gaussianMixture_identifiable_of_ae_eq
    rw [gaussianMixture_finiteProbabilityMeasure, gaussianMixture_finiteProbabilityMeasure, hdensity]
  have hlaw : finiteProbabilityMeasure θ q hq = finiteProbabilityMeasure θ p hp :=
    ProbabilityMeasure.toMeasure_injective hmeas
  have hcoeff := finiteProbabilityMeasure_coefficients_injective θ hθ q p hq hp hlaw
  intro j
  have hj := congrFun hcoeff j
  change b + t * c j = b at hj
  exact (mul_eq_zero.mp (by linarith : t * c j = 0)).resolve_left ht.ne'

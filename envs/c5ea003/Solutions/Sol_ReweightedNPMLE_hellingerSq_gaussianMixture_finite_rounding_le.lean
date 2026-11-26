-- Prove2me | solution 1 for ReweightedNPMLE.hellingerSq_gaussianMixture_finite_rounding_le
-- status  : ACCEPTED   (prove)
-- author  : @hansheng.jiang
-- created : 2026-11-26T04:07:41.820277+00:00
-- url     : https://prove2.me/submissions/73d97c4a-56c7-496b-b743-3d7bf2bae052

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Theorems.Thm_ReweightedNPMLE_gaussianKernel_comp_integrable_prod
import Theorems.Thm_ReweightedNPMLE_gaussianMixture_pos
import Theorems.Thm_ReweightedNPMLE_hellingerSq_finiteGaussianMixture_rounding

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

























theorem continuous_finiteGaussianMixture {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) : Continuous (finiteGaussianMixture w θ) := by
  unfold finiteGaussianMixture gaussianKernel
  fun_prop

theorem finiteGaussianMixture_nonneg {d : ℕ} {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (θ : ι → Point d) (hw : ∀ i, 0 ≤ w i) (x : Point d) :
    0 ≤ finiteGaussianMixture w θ x := by
  unfold finiteGaussianMixture
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (gaussianKernel_pos d x (θ i)).le









/-- Every translated Gaussian kernel is integrable. -/
theorem gaussianKernel_integrable (d : ℕ) (θ : Point d) :
    Integrable (fun x ↦ gaussianKernel d x θ) := by
  change Integrable (fun x ↦ gaussianDensity d (x - θ))
  exact (gaussianDensity_integrable d).comp_sub_right θ



/-- Every finite signed Gaussian mixture is integrable. -/
theorem finiteGaussianMixture_integrable {d : ℕ} {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (θ : ι → Point d) :
    Integrable (finiteGaussianMixture w θ) := by
  unfold finiteGaussianMixture
  exact integrable_finsetSum Finset.univ fun i _ ↦
    (gaussianKernel_integrable d (θ i)).const_mul (w i)





















end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianMixtureMeasure.
section
/-!
# Gaussian mixtures indexed by probability measures

This module connects the finite-sum Gaussian algebra to the paper's original
parameter space of arbitrary compactly supported mixing laws.
-/

open scoped BigOperators RealInnerProductSpace
open MeasureTheory

namespace ReweightedNPMLE









theorem gaussianMixture_integrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (θ : Θ → Point d) (hθ : Measurable θ) :
    Integrable (gaussianMixture μ θ) := by
  exact (gaussianKernel_comp_integrable_prod μ θ hθ).integral_prod_right

























end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.Hellinger.
section
/-!
# Squared Hellinger distance

This file formalizes the normalization convention used in the manuscript,
`H²(p,q) = ∫ (√p-√q)²`, and its affinity identity.
-/

open MeasureTheory Filter Topology

namespace ReweightedNPMLE

















/-- Integrable nonnegative densities have an integrable squared Hellinger
integrand.  This discharges a recurring analytic side condition for finite
Gaussian mixtures. -/
theorem hellingerIntegrand_integrable_of_integrable
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (p q : Ω → ℝ)
    (hpmeas : AEStronglyMeasurable p μ) (hqmeas : AEStronglyMeasurable q μ)
    (hp : ∀ᵐ x ∂μ, 0 ≤ p x) (hq : ∀ᵐ x ∂μ, 0 ≤ q x)
    (hpint : Integrable p μ) (hqint : Integrable q μ) :
    Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
  have hmeas : AEStronglyMeasurable
      (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ := by
    exact ((Real.continuous_sqrt.comp_aestronglyMeasurable hpmeas).sub
      (Real.continuous_sqrt.comp_aestronglyMeasurable hqmeas)).pow 2
  apply ((hpint.add hqint).const_mul 2).mono' hmeas
  filter_upwards [hp, hq] with x hpx hqx
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  change (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 ≤ 2 * (p x + q x)
  nlinarith [sq_nonneg (Real.sqrt (p x) + Real.sqrt (q x)),
    Real.sq_sqrt hpx, Real.sq_sqrt hqx]











/-- A squared triangle bound requiring only integrability of the three
square-root differences.  It is sufficient for the finite-net transfer and
avoids introducing an additional square-root-distance wrapper. -/
theorem hellingerSq_triangle_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (p q r : Ω → ℝ)
    (hpq : Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2) μ)
    (hqr : Integrable (fun x ↦ (Real.sqrt (q x) - Real.sqrt (r x)) ^ 2) μ)
    (hpr : Integrable (fun x ↦ (Real.sqrt (p x) - Real.sqrt (r x)) ^ 2) μ) :
    hellingerSq μ p r ≤ 2 * hellingerSq μ p q + 2 * hellingerSq μ q r := by
  unfold hellingerSq
  rw [← integral_const_mul, ← integral_const_mul,
    ← integral_add (hpq.const_mul 2) (hqr.const_mul 2)]
  apply integral_mono_ae hpr ((hpq.const_mul 2).add (hqr.const_mul 2))
  exact Filter.Eventually.of_forall fun x ↦ by
    change (Real.sqrt (p x) - Real.sqrt (r x)) ^ 2 ≤
      2 * (Real.sqrt (p x) - Real.sqrt (q x)) ^ 2 +
        2 * (Real.sqrt (q x) - Real.sqrt (r x)) ^ 2
    nlinarith [sq_nonneg ((Real.sqrt (p x) - Real.sqrt (q x)) -
      (Real.sqrt (q x) - Real.sqrt (r x)))]



























end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianMixtureHellinger.
section
/-!
# Global Hellinger control for finite Gaussian mixtures

This file combines the exact Gaussian overlap calculation with weighted
Cauchy--Schwarz.  It packages the difference of two finite mixtures as one
signed mixture and identifies its weighted `L²` error with a finite
exponential-kernel quadratic form.
-/

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

namespace ReweightedNPMLE























































theorem finiteGaussianMixture_hellingerIntegrable {d : ℕ}
    {ι : Type*} [Fintype ι] (w v : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i) :
    Integrable (fun x : Point d ↦
      (Real.sqrt (finiteGaussianMixture w θ x) -
        Real.sqrt (finiteGaussianMixture v η x)) ^ 2) :=
  hellingerIntegrand_integrable_of_integrable volume
    (finiteGaussianMixture w θ) (finiteGaussianMixture v η)
    (continuous_finiteGaussianMixture w θ).aestronglyMeasurable
    (continuous_finiteGaussianMixture v η).aestronglyMeasurable
    (Filter.Eventually.of_forall (finiteGaussianMixture_nonneg θ hw))
    (Filter.Eventually.of_forall (finiteGaussianMixture_nonneg η hv))
    (finiteGaussianMixture_integrable w θ)
    (finiteGaussianMixture_integrable v η)



end ReweightedNPMLE
end

-- Inline helpers preserved from ReweightedNPMLE.GaussianMixtureNet.
section
/-!
# Deterministic Gaussian-mixture likelihood-net estimates

This file proves the local density and log-density estimates used after the
moment-matching step of the finite likelihood-net construction.
-/

open scoped BigOperators RealInnerProductSpace

namespace ReweightedNPMLE























theorem gaussianMixture_finite_hellingerIntegrable
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (w : ι → ℝ) (z : ι → Point d) (hw : ∀ i, 0 ≤ w i) :
    MeasureTheory.Integrable (fun x : Point d ↦
      (Real.sqrt (gaussianMixture μ ϑ x) -
        Real.sqrt (finiteGaussianMixture w z x)) ^ 2) := by
  exact hellingerIntegrand_integrable_of_integrable MeasureTheory.volume
    (gaussianMixture μ ϑ) (finiteGaussianMixture w z)
    (gaussianMixture_integrable μ ϑ hϑmeas).aestronglyMeasurable
    (continuous_finiteGaussianMixture w z).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x ↦ (gaussianMixture_pos μ ϑ hϑmeas x).le)
    (Filter.Eventually.of_forall (finiteGaussianMixture_nonneg z hw))
    (gaussianMixture_integrable μ ϑ hϑmeas)
    (finiteGaussianMixture_integrable w z)





end ReweightedNPMLE
end

/-!
# Deterministic Gaussian-mixture likelihood-net estimates

This file proves the local density and log-density estimates used after the
moment-matching step of the finite likelihood-net construction.
-/

open scoped BigOperators RealInnerProductSpace

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Global Hellinger transfer from a moment-matched finite mixture to its
location-and-weight-rounded version. -/
theorem solution
    {d : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    {ι : Type*} [Fintype ι]
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (w v : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (hv : ∀ i, 0 ≤ v i)
    (hwsum : ∑ i, w i = 1) (hvsum : ∑ i, v i = 1)
    {ε q : ℝ} (hε : 0 ≤ ε) (hθη : ∀ i, ‖θ i - η i‖ ≤ ε)
    (hbase : hellingerSq MeasureTheory.volume (gaussianMixture μ ϑ)
      (finiteGaussianMixture w θ) ≤ q) :
    hellingerSq MeasureTheory.volume (gaussianMixture μ ϑ)
        (finiteGaussianMixture v η) ≤
      2 * q + ε ^ 2 + 4 * ∑ i, |w i - v i| := by
  have htri := hellingerSq_triangle_bound MeasureTheory.volume
    (gaussianMixture μ ϑ) (finiteGaussianMixture w θ)
    (finiteGaussianMixture v η)
    (gaussianMixture_finite_hellingerIntegrable μ ϑ hϑmeas w θ hw)
    (finiteGaussianMixture_hellingerIntegrable w v θ η hw hv)
    (gaussianMixture_finite_hellingerIntegrable μ ϑ hϑmeas v η hv)
  have hround := hellingerSq_finiteGaussianMixture_rounding
    w v θ η hw hv hwsum hvsum hε hθη
  calc
    hellingerSq MeasureTheory.volume (gaussianMixture μ ϑ)
        (finiteGaussianMixture v η) ≤
        2 * hellingerSq MeasureTheory.volume (gaussianMixture μ ϑ)
            (finiteGaussianMixture w θ) +
          2 * hellingerSq MeasureTheory.volume
            (finiteGaussianMixture w θ) (finiteGaussianMixture v η) := htri
    _ ≤ 2 * q + 2 * (ε ^ 2 / 2 + 2 * ∑ i, |w i - v i|) :=
      add_le_add (mul_le_mul_of_nonneg_left hbase (by norm_num))
        (mul_le_mul_of_nonneg_left hround (by norm_num))
    _ = 2 * q + ε ^ 2 + 4 * ∑ i, |w i - v i| := by ring

-- Prove2me | solution 1 for ReweightedNPMLE.sqrt_sub_sq_finiteGaussianMixture_le_sum
-- status  : ACCEPTED   (prove)
-- author  : @Hansheng Jiang
-- created : 2026-11-26T04:04:18.18259+00:00
-- url     : https://prove2.me/submissions/c31c1414-b9c1-4d04-87a5-eebe36fe5268

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
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



























theorem finiteGaussianMixture_nonneg {d : ℕ} {ι : Type*} [Fintype ι]
    {w : ι → ℝ} (θ : ι → Point d) (hw : ∀ i, 0 ≤ w i) (x : Point d) :
    0 ≤ finiteGaussianMixture w θ x := by
  unfold finiteGaussianMixture
  exact Finset.sum_nonneg fun i _ ↦ mul_nonneg (hw i) (gaussianKernel_pos d x (θ i)).le



































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





theorem sqrt_sub_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (Real.sqrt a - Real.sqrt b) ^ 2 = a + b - 2 * Real.sqrt (a * b) := by
  rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_mul ha]
  ring



















































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













































theorem sqrt_weighted_kernel_product {d : ℕ}
    (a : ℝ) (ha : 0 ≤ a) (x θ η : Point d) :
    Real.sqrt (a * gaussianKernel d x θ) *
        Real.sqrt (a * gaussianKernel d x η) =
      a * Real.sqrt (gaussianKernel d x θ * gaussianKernel d x η) := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul ha,
    Real.sqrt_mul (gaussianKernel_pos d x θ).le]
  have hsqa : Real.sqrt a * Real.sqrt a = a := by
    rw [← pow_two, Real.sq_sqrt ha]
  calc
    Real.sqrt a * Real.sqrt (gaussianKernel d x θ) *
        (Real.sqrt a * Real.sqrt (gaussianKernel d x η)) =
        (Real.sqrt a * Real.sqrt a) *
          (Real.sqrt (gaussianKernel d x θ) *
            Real.sqrt (gaussianKernel d x η)) := by ring
    _ = a * (Real.sqrt (gaussianKernel d x θ) *
        Real.sqrt (gaussianKernel d x η)) := by rw [hsqa]













end ReweightedNPMLE
end

/-!
# Global Hellinger control for finite Gaussian mixtures

This file combines the exact Gaussian overlap calculation with weighted
Cauchy--Schwarz.  It packages the difference of two finite mixtures as one
signed mixture and identifies its weighted `L²` error with a finite
exponential-kernel quadratic form.
-/

open MeasureTheory
open scoped BigOperators RealInnerProductSpace

open ReweightedNPMLE
open ReweightedNPMLE in
/-- Joint convexity of the squared Hellinger integrand, specialized to
finite Gaussian mixtures with common weights. -/
theorem solution {d : ℕ}
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (x : Point d) :
    (Real.sqrt (finiteGaussianMixture w θ x) -
        Real.sqrt (finiteGaussianMixture w η x)) ^ 2 ≤
      ∑ i, w i *
        (Real.sqrt (gaussianKernel d x (θ i)) -
          Real.sqrt (gaussianKernel d x (η i))) ^ 2 := by
  have hp : 0 ≤ finiteGaussianMixture w θ x :=
    finiteGaussianMixture_nonneg θ hw x
  have hq : 0 ≤ finiteGaussianMixture w η x :=
    finiteGaussianMixture_nonneg η hw x
  have hcs0 := Real.sum_sqrt_mul_sqrt_le Finset.univ
    (f := fun i ↦ w i * gaussianKernel d x (θ i))
    (g := fun i ↦ w i * gaussianKernel d x (η i))
    (fun i ↦ mul_nonneg (hw i) (gaussianKernel_pos d x (θ i)).le)
    (fun i ↦ mul_nonneg (hw i) (gaussianKernel_pos d x (η i)).le)
  have hcs :
      ∑ i, w i * Real.sqrt
          (gaussianKernel d x (θ i) * gaussianKernel d x (η i)) ≤
        Real.sqrt (finiteGaussianMixture w θ x) *
          Real.sqrt (finiteGaussianMixture w η x) := by
    calc
      ∑ i, w i * Real.sqrt
          (gaussianKernel d x (θ i) * gaussianKernel d x (η i)) =
          ∑ i, Real.sqrt (w i * gaussianKernel d x (θ i)) *
            Real.sqrt (w i * gaussianKernel d x (η i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (sqrt_weighted_kernel_product (w i) (hw i) x (θ i) (η i)).symm
      _ ≤ Real.sqrt (∑ i, w i * gaussianKernel d x (θ i)) *
          Real.sqrt (∑ i, w i * gaussianKernel d x (η i)) := hcs0
      _ = Real.sqrt (finiteGaussianMixture w θ x) *
          Real.sqrt (finiteGaussianMixture w η x) := rfl
  rw [sqrt_sub_sq hp hq]
  simp_rw [sqrt_sub_sq (gaussianKernel_pos d x _).le
    (gaussianKernel_pos d x _).le]
  unfold finiteGaussianMixture
  unfold finiteGaussianMixture at hcs
  rw [Real.sqrt_mul (Finset.sum_nonneg fun i _ ↦
    mul_nonneg (hw i) (gaussianKernel_pos d x (θ i)).le)]
  calc
    ∑ i, w i * gaussianKernel d x (θ i) +
          ∑ i, w i * gaussianKernel d x (η i) -
        2 * (Real.sqrt (∑ i, w i * gaussianKernel d x (θ i)) *
          Real.sqrt (∑ i, w i * gaussianKernel d x (η i))) ≤
        ∑ i, w i * gaussianKernel d x (θ i) +
          ∑ i, w i * gaussianKernel d x (η i) -
        2 * ∑ i, w i * Real.sqrt
          (gaussianKernel d x (θ i) * gaussianKernel d x (η i)) := by
      nlinarith
    _ = ∑ i, w i *
        (gaussianKernel d x (θ i) + gaussianKernel d x (η i) -
          2 * Real.sqrt
            (gaussianKernel d x (θ i) * gaussianKernel d x (η i))) := by
      simp_rw [mul_sub, mul_add]
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring

-- Prove2me | Theorems.Thm_ReweightedNPMLE_sqrt_sub_sq_finiteGaussianMixture_le_sum
-- name    : ReweightedNPMLE.sqrt_sub_sq_finiteGaussianMixture_le_sum
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:41:10.453618+00:00
-- url     : https://prove2.me/theorems/fd9249c1-2a65-53b9-9f30-ddf316d34564
-- title:
--   Pointwise convexity of the Gaussian Hellinger integrand
-- statement:
--   Write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\), and for a finite index set \(I\) write \(f_{w,\theta}(x)=\sum_{i\in I}w_i\phi_d(x-\theta_i)\). If \(w_i\ge0\), then for every \(x\in\mathbb R^d\) and arbitrary pairs of locations \(\theta_i,\eta_i\),
--   \[
--   \bigl(\sqrt{f_{w,\theta}(x)}-\sqrt{f_{w,\eta}(x)}\bigr)^2
--   \le\sum_i w_i\bigl(\sqrt{\phi_d(x-\theta_i)}
--   -\sqrt{\phi_d(x-\eta_i)}\bigr)^2.
--   \]
--   No assumption that the weights sum to one is needed. This is the pointwise joint convexity estimate used to control a mixture by its paired components.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureHellinger.lean#L514-L576

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

theorem ReweightedNPMLE.sqrt_sub_sq_finiteGaussianMixture_le_sum {d : ℕ}
    {ι : Type*} [Fintype ι] (w : ι → ℝ) (θ η : ι → Point d)
    (hw : ∀ i, 0 ≤ w i) (x : Point d) :
    (Real.sqrt (finiteGaussianMixture w θ x) -
        Real.sqrt (finiteGaussianMixture w η x)) ^ 2 ≤
      ∑ i, w i *
        (Real.sqrt (gaussianKernel d x (θ i)) -
          Real.sqrt (gaussianKernel d x (η i))) ^ 2 := by sorry

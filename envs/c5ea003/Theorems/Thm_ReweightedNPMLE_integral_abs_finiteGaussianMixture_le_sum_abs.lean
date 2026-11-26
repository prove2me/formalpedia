-- Prove2me | Theorems.Thm_ReweightedNPMLE_integral_abs_finiteGaussianMixture_le_sum_abs
-- name    : ReweightedNPMLE.integral_abs_finiteGaussianMixture_le_sum_abs
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:41:03.033707+00:00
-- url     : https://prove2.me/theorems/50542640-0600-56e1-bcff-0ae97a720801
-- title:
--   An L¹ bound for signed Gaussian mixtures
-- statement:
--   Write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\), and for a finite index set \(I\) write \(f_{w,\theta}(x)=\sum_{i\in I}w_i\phi_d(x-\theta_i)\). For arbitrary real coefficients \(c_i\) and locations \(\theta_i\in\mathbb R^d\),
--   \[
--   \int_{\mathbb R^d}|f_{c,\theta}(x)|\,dx\le \sum_{i\in I}|c_i|.
--   \]
--   No positivity or normalization condition is imposed on the coefficients, and locations need not be bounded. Thus the map from signed mixing coefficients to the resulting Gaussian mixture is contractive from the coefficient \(\ell^1\) norm to the density \(L^1\) norm.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureHellinger.lean#L324-L351

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

theorem ReweightedNPMLE.integral_abs_finiteGaussianMixture_le_sum_abs
    {d : ℕ} {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (θ : ι → Point d) :
    ∫ x, |finiteGaussianMixture c θ x| ≤ ∑ i, |c i| := by sorry

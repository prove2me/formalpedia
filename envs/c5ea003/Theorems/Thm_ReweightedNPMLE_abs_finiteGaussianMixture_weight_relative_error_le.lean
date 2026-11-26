-- Prove2me | Theorems.Thm_ReweightedNPMLE_abs_finiteGaussianMixture_weight_relative_error_le
-- name    : ReweightedNPMLE.abs_finiteGaussianMixture_weight_relative_error_le
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:36:25.2438+00:00
-- url     : https://prove2.me/theorems/f616387d-1568-591c-9485-b6691d6adea7
-- title:
--   Relative Gaussian-mixture error under weight perturbations
-- statement:
--   Write \(\phi_d(x)=(2\pi)^{-d/2}e^{-\|x\|^2/2}\) and \(f_{w,\theta}(x)=\sum_iw_i\phi_d(x-\theta_i)\) for a finite index set \(I\). Assume \(w_i\ge0\), \(\sum_iw_i=1\), \(T,S\ge0\), \(\|x\|\le T\), and \(\|\theta_i\|\le S\) for every \(i\). The coefficients \(v_i\) may be arbitrary real numbers. Put \(B=TS+S^2/2\). Then
--   \[
--   \left|\frac{f_{v,\theta}(x)}{f_{w,\theta}(x)}-1\right|
--   \le e^{2B}\sum_i|v_i-w_i|.
--   \]
--   The reference mixture is positive; positivity or normalization of the perturbed coefficients is not required for this algebraic relative-error estimate.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureNet.lean#L201-L271

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

/-!
# Deterministic Gaussian-mixture likelihood-net estimates

This file proves the local density and log-density estimates used after the
moment-matching step of the finite likelihood-net construction.
-/

open scoped BigOperators RealInnerProductSpace

open ReweightedNPMLE

theorem ReweightedNPMLE.abs_finiteGaussianMixture_weight_relative_error_le
    {d : ℕ} {ι : Type*} [Fintype ι]
    (w v : ι → ℝ) (θ : ι → Point d) (x : Point d)
    (hw : ∀ i, 0 ≤ w i) (hwsum : ∑ i, w i = 1)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hx : ‖x‖ ≤ T) (hθ : ∀ i, ‖θ i‖ ≤ S) :
    |finiteGaussianMixture v θ x / finiteGaussianMixture w θ x - 1| ≤
      Real.exp (2 * (T * S + S ^ 2 / 2)) * ∑ i, |v i - w i| := by sorry

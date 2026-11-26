-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianKernel_location_exp_bounds
-- name    : ReweightedNPMLE.gaussianKernel_location_exp_bounds
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:36:36.815067+00:00
-- url     : https://prove2.me/theorems/e82cff4e-2b83-4037-b4a5-6874c03a769a
-- title:
--   Multiplicative comparison of nearby Gaussian kernels
-- statement:
--   Let \(\phi_d\) be the standard Gaussian density. Suppose \(T,S,\varepsilon\ge0\), \(\|x\|\le T\), \(\|\theta\|,\|\eta\|\le S\), and \(\|\theta-\eta\|\le\varepsilon\). Then
--   \[
--   e^{-(T+S)\varepsilon}\phi_d(x-\theta)
--   \le\phi_d(x-\eta)
--   \le e^{(T+S)\varepsilon}\phi_d(x-\theta).
--   \]
--   Both inequalities hold pointwise and have the same exponent, so the relative effect of a location perturbation is controlled uniformly on the observation ball.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureNet.lean#L104-L145

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

theorem ReweightedNPMLE.gaussianKernel_location_exp_bounds {d : ℕ} (x θ η : Point d)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ‖θ‖ ≤ S) (hη : ‖η‖ ≤ S)
    (hθη : ‖θ - η‖ ≤ ε) :
    Real.exp (-((T + S) * ε)) * gaussianKernel d x θ ≤
        gaussianKernel d x η ∧
      gaussianKernel d x η ≤
        Real.exp ((T + S) * ε) * gaussianKernel d x θ := by sorry

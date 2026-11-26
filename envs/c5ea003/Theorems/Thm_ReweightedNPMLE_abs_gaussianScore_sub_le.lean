-- Prove2me | Theorems.Thm_ReweightedNPMLE_abs_gaussianScore_sub_le
-- name    : ReweightedNPMLE.abs_gaussianScore_sub_le
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:35:59.216745+00:00
-- url     : https://prove2.me/theorems/eb357a49-e37d-484a-9a14-11d8e88e0a99
-- title:
--   Lipschitz control of the Gaussian score in its location
-- statement:
--   For \(x,\theta\in\mathbb R^d\), define \(s(x,\theta)=\langle x,\theta\rangle-\|\theta\|^2/2\). Suppose \(T,S,\varepsilon\ge0\), \(\|x\|\le T\), \(\|\theta\|,\|\eta\|\le S\), and \(\|\theta-\eta\|\le\varepsilon\). Then
--   \[
--   |s(x,\theta)-s(x,\eta)|\le(T+S)\varepsilon.
--   \]
--   Thus on a radius-\(T\) observation ball, moving a Gaussian location within a radius-\(S\) parameter ball changes the log kernel ratio by at most a constant times the location displacement.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureNet.lean#L15-L51

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

theorem ReweightedNPMLE.abs_gaussianScore_sub_le {d : ℕ} (x θ η : Point d)
    {T S ε : ℝ} (hT : 0 ≤ T) (_hS : 0 ≤ S) (hε : 0 ≤ ε)
    (hx : ‖x‖ ≤ T) (hθ : ‖θ‖ ≤ S) (hη : ‖η‖ ≤ S)
    (hθη : ‖θ - η‖ ≤ ε) :
    |gaussianScore x θ - gaussianScore x η| ≤ (T + S) * ε := by sorry

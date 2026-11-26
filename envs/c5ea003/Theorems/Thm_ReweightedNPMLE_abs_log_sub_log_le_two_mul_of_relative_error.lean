-- Prove2me | Theorems.Thm_ReweightedNPMLE_abs_log_sub_log_le_two_mul_of_relative_error
-- name    : ReweightedNPMLE.abs_log_sub_log_le_two_mul_of_relative_error
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:35:47.948922+00:00
-- url     : https://prove2.me/theorems/1ce54756-1c89-5b25-b2ef-12a059f4420b
-- title:
--   Converting a small relative error to a log error
-- statement:
--   Let \(a,b>0\) and \(0\le\delta\le1/2\). If
--   \[
--   \left|\frac ab-1\right|\le\delta,
--   \]
--   then
--   \[
--   |\log a-\log b|\le2\delta.
--   \]
--   The hypothesis controls the error relative to the denominator \(b\). Positivity of both numbers and the upper bound on \(\delta\) ensure that the logarithmic comparison is finite and uniformly controlled.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureNet.lean#L53-L74

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

theorem ReweightedNPMLE.abs_log_sub_log_le_two_mul_of_relative_error
    {a b δ : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hδ : 0 ≤ δ) (hδhalf : δ ≤ 1 / 2)
    (hrel : |a / b - 1| ≤ δ) :
    |Real.log a - Real.log b| ≤ 2 * δ := by sorry

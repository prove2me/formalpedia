-- Prove2me | Theorems.Thm_ReweightedNPMLE_gaussianMomentHellingerError_le_stirling
-- name    : ReweightedNPMLE.gaussianMomentHellingerError_le_stirling
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:44:40.984923+00:00
-- url     : https://prove2.me/theorems/2b7efb86-6424-4214-8e0f-c02623be45ad
-- title:
--   A Stirling bound for the global Gaussian moment error
-- statement:
--   Let
--   \[
--   h_L(S)=\left(\frac{4e^{S^2}(S^2)^{2L+1}}{(2L+1)!}\right)^{1/2}.
--   \]
--   For every \(S\ge0\) and nonnegative integer \(L\),
--   \[
--   h_L(S)\le
--   \left[4e^{S^2}\left(\frac{eS^2}{2L+1}\right)^{2L+1}\right]^{1/2}.
--   \]
--   The quantity \(h_L(S)\) is the bound used for the squared-Hellinger error of moment matching.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianNearMLERate.lean#L618-L649

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_GaussianNearMLE
import Definitions.Def_ReweightedNPMLE_GaussianNearMLERate
import Definitions.Def_ReweightedNPMLE_GaussianRadius
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Explicit entropy arithmetic for the Gaussian near-MLE theorem

This module turns the finite Gaussian-mixture net cardinality appearing in
`GaussianNearMLE` into the binomial and logarithmic bounds used in the
paper's rate calculation.  It is kept separate from the probabilistic
argument so that the remaining asymptotic tuning can use a small, explicit
arithmetic interface.
-/

open scoped ENNReal
open Filter Topology MeasureTheory Set

open ReweightedNPMLE

theorem ReweightedNPMLE.gaussianMomentHellingerError_le_stirling {S : ℝ} (hS : 0 ≤ S)
    (L : ℕ) :
    gaussianMomentHellingerError S L ≤
      (4 * Real.exp (S ^ 2) *
        (Real.exp 1 * S ^ 2 / (2 * L + 1)) ^ (2 * L + 1)) ^
          (1 / 2 : ℝ) := by sorry

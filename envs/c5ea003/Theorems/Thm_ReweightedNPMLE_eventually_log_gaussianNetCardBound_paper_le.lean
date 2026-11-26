-- Prove2me | Theorems.Thm_ReweightedNPMLE_eventually_log_gaussianNetCardBound_paper_le
-- name    : ReweightedNPMLE.eventually_log_gaussianNetCardBound_paper_le
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:46:14.131858+00:00
-- url     : https://prove2.me/theorems/1469133f-0e3b-59cb-b47b-d3ac437899a3
-- title:
--   An explicit polylogarithmic entropy bound for the Gaussian mixture net
-- statement:
--   Write \(a_n=\log n/\log\log n\) and \(L_C(n)=\lceil Ca_n\rceil_+\),
--   where \(\lceil x\rceil_+=\max\{0,\lceil x\rceil\}\). For fixed \(d\ge0,C>0,S\ge0\), set \(L_n=L_C(n)\),
--   \(k_n=\binom{2L_n+d}{d}\), \(M_n=\lceil k_n n^{16}\rceil_+\),
--   \(\varepsilon_n=n^{-16}\), \(c_n=\lfloor2S(d+2)/\varepsilon_n\rfloor+1\), and
--   \(N_n=(c_n^d)^{k_n+1}(M_n+1)^{k_n}\).
--   For all sufficiently large integers \(n\),
--   \[
--   \log N_n\le17(d+1)\bigl((4C+1)^d+1\bigr)a_n^d\log n.
--   \]
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianNearMLERate.lean#L1044-L1139

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

theorem ReweightedNPMLE.eventually_log_gaussianNetCardBound_paper_le
    (d : ℕ) {C S : ℝ} (hC : 0 < C) (hS : 0 ≤ S) :
    ∀ᶠ n in Filter.atTop,
      Real.log (gaussianNetCardBound d (gaussianPaperMomentOrder C n)
        (gaussianPaperWeightDenominator d C n) S
        (gaussianPaperEpsilon n) : ℝ) ≤
      17 * ((d : ℝ) + 1) * ((4 * C + 1) ^ d + 1) *
        gaussianPaperLogScale n ^ d * Real.log (n : ℝ) := by sorry

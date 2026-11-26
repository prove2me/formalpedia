-- Prove2me | Theorems.Thm_ReweightedNPMLE_eventually_gaussianNearMLE_threshold_256_le
-- name    : ReweightedNPMLE.eventually_gaussianNearMLE_threshold_256_le
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:47:34.645094+00:00
-- url     : https://prove2.me/theorems/3a32929c-42a1-4048-bbb0-8423ddc07d91
-- title:
--   The explicit near-MLE threshold is bounded by the displayed polylogarithmic rate
-- statement:
--   Write \(a_n=\log n/\log\log n\) and \(L_C(n)=\lceil Ca_n\rceil_+\),
--   where \(\lceil x\rceil_+=\max\{0,\lceil x\rceil\}\). Let
--   \[
--   h_L(S)=\left(\frac{4e^{S^2}(S^2)^{2L+1}}{(2L+1)!}\right)^{1/2}.
--   \]
--   Fix \(d\ge0,S,b\ge0\). Put \(L_n=L_{256}(n)\),
--   \(k_n=\binom{2L_n+d}{d}\), \(M_n=\lceil k_n n^{16}\rceil_+\),
--   \(\varepsilon_n=n^{-16}\), \(g_n=2h_{L_n}(S)+\varepsilon_n^2+8k_n/M_n\), and
--   \(N_n=((\lfloor2S(d+2)/\varepsilon_n\rfloor+1)^d)^{k_n+1}(M_n+1)^{k_n}\).
--   Define \(E_d=17(d+1)(1025^d+1)\) and \(C_{d,b}=22+4(E_d+b+4)\).
--   Then, for all sufficiently large integers \(n\),
--   \[
--   2g_n+\frac{4(\log N_n+(b+2)\log n+2)}n
--   \le C_{d,b}\frac{a_n^d\log n}{n}.
--   \]
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianNearMLERate.lean#L1149-L1242

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

theorem ReweightedNPMLE.eventually_gaussianNearMLE_threshold_256_le
    (d : ℕ) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b) :
    ∀ᶠ n : ℕ in Filter.atTop,
      2 * gaussianNetHellingerSqError d (gaussianPaperMomentOrder 256 n)
          (gaussianPaperWeightDenominator d 256 n) S
          (gaussianPaperEpsilon n) +
        4 * (Real.log (gaussianNetCardBound d
            (gaussianPaperMomentOrder 256 n)
            (gaussianPaperWeightDenominator d 256 n) S
            (gaussianPaperEpsilon n) : ℝ) +
          (b + 2) * Real.log (n : ℝ) + 2) / n ≤
      gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d *
        Real.log (n : ℝ) / n := by sorry

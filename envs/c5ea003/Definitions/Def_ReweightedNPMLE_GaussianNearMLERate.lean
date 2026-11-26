-- Prove2me | Definitions.Def_ReweightedNPMLE_GaussianNearMLERate
-- name    : ReweightedNPMLE_GaussianNearMLERate
-- status  : Definition
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:25:30.364006+00:00
-- url     : https://prove2.me/theorems/eaaf6173-262c-52dd-b058-b4dfd165bd87
-- title:
--   Explicit tuning parameters for the Gaussian near-MLE rate
-- statement:
--   Define the logarithmic scale and rounded Taylor order by
--   \[
--   a_n=\frac{\log n}{\log\log n},\qquad L_C(n)=\lceil Ca_n\rceil_+,
--   \]
--   where \(\lceil t\rceil_+=\max\{0,\lceil t\rceil\}\).
--   The location mesh is \(\varepsilon_n=n^{-16}\), and the weight denominator is
--   \(M_{d,C,n}=\lceil\binom{2L_C(n)+d}{d}n^{16}\rceil_+\).
--   The radius exponent is \(R_{b,n}=(b+4)\log n\), giving
--   \[
--   T_{d,S,b,n}=S+\sqrt d\,\sqrt{2R_{b,n}},\quad
--   A_{d,S,b,n}=T_{d,S,b,n}S+S^2/2,\quad
--   D_{d,S,b}=\tfrac32S^2+\sqrt d\,\sqrt{2(b+4)}S.
--   \]
--   Finally, the entropy and risk coefficients at order constant \(256\) are
--   \[
--   E_d=17(d+1)(1025^d+1),\qquad C_{d,b}=22+4(E_d+b+4).
--   \]
--   These definitions specify every tuning quantity used in the eventual near-MLE bound.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianNearMLERate.lean#L22-L1147

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

namespace ReweightedNPMLE

/-- The logarithmic scale used for the paper's Taylor order.  Values at the
finitely many small sample sizes are immaterial to the eventual statements. -/
noncomputable def gaussianPaperLogScale (n : ℕ) : ℝ :=
  Real.log n / Real.log (Real.log n)

/-- Paper Taylor order with an explicit multiplicative constant. -/
noncomputable def gaussianPaperMomentOrder (C : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil (C * gaussianPaperLogScale n)

/-- Location mesh used in the paper's finite likelihood net. -/
noncomputable def gaussianPaperEpsilon (n : ℕ) : ℝ :=
  ((n : ℝ) ^ 16)⁻¹

/-- Weight-grid denominator `ceil(k n^16)` from the paper, where `k` is the
moment dimension at the chosen Taylor order. -/
noncomputable def gaussianPaperWeightDenominator
    (d : ℕ) (C : ℝ) (n : ℕ) : ℕ :=
  Nat.ceil ((gaussianMomentDimension d (gaussianPaperMomentOrder C n) : ℝ) *
    (n : ℝ) ^ 16)















/-- Radius exponent used to make the Gaussian sample-radius failure
polynomially small. -/
noncomputable def gaussianPaperRadiusExponent (b : ℝ) (n : ℕ) : ℝ :=
  (b + 4) * Real.log (n : ℝ)

/-- Deterministic sample radius paired with `gaussianPaperRadiusExponent`. -/
noncomputable def gaussianPaperSampleRadius
    (d : ℕ) (S b : ℝ) (n : ℕ) : ℝ :=
  S + Real.sqrt (d : ℝ) * Real.sqrt (2 * gaussianPaperRadiusExponent b n)

/-- Argument of the local exponential Taylor remainder. -/
noncomputable def gaussianPaperTaylorArgument
    (d : ℕ) (S b : ℝ) (n : ℕ) : ℝ :=
  gaussianPaperSampleRadius d S b n * S + S ^ 2 / 2

/-- A fixed coefficient controlling the growing Taylor argument. -/
noncomputable def gaussianPaperTaylorConstant (d : ℕ) (S b : ℝ) : ℝ :=
  3 * S ^ 2 / 2 +
    Real.sqrt (d : ℝ) * Real.sqrt (2 * (b + 4)) * S





































































/-- Explicit entropy coefficient at the fixed Taylor constant `256`. -/
noncomputable def gaussianPaperEntropyConstant (d : ℕ) : ℝ :=
  17 * ((d : ℝ) + 1) * ((1025 : ℝ) ^ d + 1)

/-- Displayed constant in the final Hellinger-rate theorem. -/
noncomputable def gaussianPaperRateConstant (d : ℕ) (b : ℝ) : ℝ :=
  22 + 4 * (gaussianPaperEntropyConstant d + b + 4)







end ReweightedNPMLE



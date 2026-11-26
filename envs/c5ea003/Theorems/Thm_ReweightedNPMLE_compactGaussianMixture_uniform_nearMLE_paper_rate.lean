-- Prove2me | Theorems.Thm_ReweightedNPMLE_compactGaussianMixture_uniform_nearMLE_paper_rate
-- name    : ReweightedNPMLE.compactGaussianMixture_uniform_nearMLE_paper_rate
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:47:58.396226+00:00
-- url     : https://prove2.me/theorems/1a49ea5e-ea06-53b7-aa17-0e1601b678c1
-- title:
--   Uniform polynomial-tail Hellinger rate for all compact Gaussian near-MLEs
-- statement:
--   For a probability measure \(G\) on \(K\subseteq\mathbb R^d\), let
--   \(f_G(x)=\int_K(2\pi)^{-d/2}e^{-\|x-\theta\|^2/2}\,dG(\theta)\),
--   \(\ell_n(G)=\sum_{i=1}^n\log f_G(X_i)\), and
--   \(H^2(f,g)=\int_{\mathbb R^d}(\sqrt f-\sqrt g)^2\,dx\).
--   Samples are independent with density \(f_{G_\star}\), and \(\mathbb P^*\) denotes outer probability. Fix an integer \(d>0\), a compact nonempty
--   \(K\subseteq\mathbb R^d\), and \(S,b\ge0\) such that \(\|\theta\|\le S\) on \(K\).
--   Put \(a_n=\log n/\log\log n\) and
--   \[
--   C_{d,b}=22+4\bigl(17(d+1)(1025^d+1)+b+4\bigr).
--   \]
--   There exists an integer \(n_0\), independent of \(G_\star\), such that for every
--   \(n\ge n_0\) and every \(G_\star\in\mathcal P(K)\),
--   \[
--   \mathbb P^*\{\exists G\in\mathcal P(K):
--   \ell_n(G)\ge\ell_n(G_\star)-1,\
--   H^2(f_G,f_{G_\star})>C_{d,b}a_n^d\log n/n\}
--   \le(2d+1)n^{-(b+2)}.
--   \]
--   The uniformity includes all probability mixing laws supported on \(K\).
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianNearMLERate.lean#L1289-L1401

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

theorem ReweightedNPMLE.compactGaussianMixture_uniform_nearMLE_paper_rate
    {d : ℕ} (hd : 0 < d)
    (K : Set (Point d)) (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ Gstar : ProbabilityMeasure K,
      (Measure.pi (fun _ : Fin n ↦ volume.withDensity (fun y ↦
        ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))).real
          {x | ∃ G : ProbabilityMeasure K,
            (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
                ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
            gaussianPaperRateConstant d b * gaussianPaperLogScale n ^ d *
                Real.log (n : ℝ) / n <
              hellingerSq volume (compactGaussianMixtureDensity G)
                (compactGaussianMixtureDensity Gstar)} ≤
        (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) := by sorry

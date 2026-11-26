-- Prove2me | Theorems.Thm_ReweightedNPMLE_compactGaussianSampleMeasure_paper_radius_tail
-- name    : ReweightedNPMLE.compactGaussianSampleMeasure_paper_radius_tail
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:45:32.197037+00:00
-- url     : https://prove2.me/theorems/f62a3cb2-436e-48c6-a055-eadf7199611a
-- title:
--   A uniform polynomial tail bound for the Gaussian-mixture sample radius
-- statement:
--   For a probability measure \(G\) on \(K\subseteq\mathbb R^d\), let
--   \(f_G(x)=\int_K(2\pi)^{-d/2}e^{-\|x-\theta\|^2/2}\,dG(\theta)\),
--   \(\ell_n(G)=\sum_{i=1}^n\log f_G(X_i)\), and
--   \(H^2(f,g)=\int_{\mathbb R^d}(\sqrt f-\sqrt g)^2\,dx\).
--   Samples are independent with density \(f_{G_\star}\), and \(\mathbb P^*\) denotes outer probability. Let \(K\subseteq\mathbb R^d\) be any set, let
--   \(G_\star\in\mathcal P(K)\), and suppose \(S,b\ge0\) and
--   \(\|\theta\|\le S\) for every \(\theta\in K\). For any integer \(n\ge1\) with
--   \(\log n>0\), set \(T_n=S+\sqrt d\,\sqrt{2(b+4)\log n}\). Then
--   \[
--   \mathbb P\{\exists i\in\{1,\ldots,n\}:\|X_i\|>T_n\}
--   \le(2d+1)n^{-(b+2)}.
--   \]
--   Compactness of \(K\) is not required.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianSampling.lean#L49-L72

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
import Mathlib.MeasureTheory.Constructions.Pi
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
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
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
import Definitions.Def_ReweightedNPMLE_GaussianSampling
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Gaussian sample laws and simultaneous genericity

The iid sample law has a density, is a probability law, and satisfies the
uniform paper-radius tail. The constants do not depend on the true compact
mixing law.
-/

open Set Filter MeasureTheory ProbabilityTheory
open scoped Topology ENNReal

open ReweightedNPMLE

theorem ReweightedNPMLE.compactGaussianSampleMeasure_paper_radius_tail {d n : ℕ} {K : Set (Point d)}
    (Gstar : ProbabilityMeasure K) {S b : ℝ} (hS : 0 ≤ S) (hb : 0 ≤ b)
    (hKbound : ∀ a ∈ K, ‖a‖ ≤ S) (hlog : 0 < Real.log (n : ℝ)) (hn : 1 ≤ n) :
    (compactGaussianSampleMeasure Gstar n).real
      {x | ∃ i, gaussianPaperSampleRadius d S b n < ‖x i‖} ≤
        (2 * (d : ℝ) + 1) * (n : ℝ) ^ (-(b + 2)) := by sorry

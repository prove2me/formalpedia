-- Prove2me | Theorems.Thm_ReweightedNPMLE_compactGaussianMixture_uniform_nearMLE_bad_event_bound_entropy_tuned
-- name    : ReweightedNPMLE.compactGaussianMixture_uniform_nearMLE_bad_event_bound_entropy_tuned
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:47:23.530045+00:00
-- url     : https://prove2.me/theorems/70e74c95-43b6-4801-88c4-3f9a9e5a6846
-- title:
--   Entropy-tuned uniform near-MLE bound for compact Gaussian mixtures
-- statement:
--   For a probability measure \(G\) on \(K\subseteq\mathbb R^d\), let
--   \(f_G(x)=\int_K(2\pi)^{-d/2}e^{-\|x-\theta\|^2/2}\,dG(\theta)\),
--   \(\ell_n(G)=\sum_{i=1}^n\log f_G(X_i)\), and
--   \(H^2(f,g)=\int_{\mathbb R^d}(\sqrt f-\sqrt g)^2\,dx\).
--   Samples are independent with density \(f_{G_\star}\), and \(\mathbb P^*\) denotes outer probability. Let \(n>0\), let \(K\) be compact and nonempty and bounded in norm
--   by \(S\ge0\), and choose \(\varepsilon>0,r>0\). Set \(T=S+\sqrt d\,r\). For integers \(L\ge0,M>0\), put
--   \[
--   k=\binom{2L+d}{d},\quad a=TS+S^2/2,\quad
--   h=\left(\frac{4e^{S^2}(S^2)^{2L+1}}{(2L+1)!}\right)^{1/2},\quad
--   \rho=\frac{2e^{2a}a^{L+1}}{(L+1)!},
--   \]
--   \[
--   g=2h+\varepsilon^2+8k/M,\qquad
--   \delta=(T+S)\varepsilon+4e^{2a}k/M+2\rho.
--   \]
--   Define
--   \(c=\lfloor2S(d+2)/\varepsilon\rfloor+1\) and
--   \(N=(c^d)^{k+1}(M+1)^k\).
--   Assume \(\rho\le1/2\), \(2e^{2a}k/M\le1/2\), and \(n\delta\le1\).
--   For every \(G_\star\in\mathcal P(K)\) and \(B\ge0\),
--   \[
--   \mathbb P^*\{\exists G\in\mathcal P(K):
--   \ell_n(G)\ge\ell_n(G_\star)-1,\
--   H^2(f_G,f_{G_\star})>2g+4(\log N+B+2)/n\}
--   \le2nd\,e^{-r^2/2}+e^{-B-1}.
--   \]
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianNearMLE.lean#L373-L440

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
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
# Uniform near-MLE control for compact Gaussian mixtures

This module closes the main interface between the analytic Gaussian-mixture
net and the finite likelihood-ratio test.  Candidates are genuine bundled
probability measures on a compact location set, rather than a finite-mixture
surrogate parameterization.
-/

open scoped BigOperators ENNReal
open MeasureTheory Set

open ReweightedNPMLE

theorem ReweightedNPMLE.compactGaussianMixture_uniform_nearMLE_bad_event_bound_entropy_tuned
    {d L M n : ℕ} (hn : 0 < n)
    (K : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    {S ε r B : ℝ} (hS : 0 ≤ S) (hε : 0 < ε) (hr : 0 < r)
    (hB : 0 ≤ B)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S)
    (hM : 0 < M)
    (hrelativeHalf : gaussianMomentRelativeError
      (S + Real.sqrt d * r) S L ≤ 1 / 2)
    (hweightSmall : Real.exp
      (2 * ((S + Real.sqrt d * r) * S + S ^ 2 / 2)) *
        (2 * gaussianMomentDimension d L / M) ≤ 1 / 2)
    (Gstar : ProbabilityMeasure K)
    (hnδ : (n : ℝ) * gaussianNetLogError d L M
      (S + Real.sqrt d * r) S ε ≤ 1) :
    (Measure.pi (fun _ : Fin n ↦ volume.withDensity (fun y ↦
      ENNReal.ofReal (compactGaussianMixtureDensity Gstar y)))).real
        {x | ∃ G : ProbabilityMeasure K,
          (∑ i, Real.log (compactGaussianMixtureDensity Gstar (x i))) - 1 ≤
              ∑ i, Real.log (compactGaussianMixtureDensity G (x i)) ∧
          2 * gaussianNetHellingerSqError d L M S ε +
              4 * (Real.log (gaussianNetCardBound d L M S ε) + B + 2) / n <
            hellingerSq volume (compactGaussianMixtureDensity G)
              (compactGaussianMixtureDensity Gstar)} ≤
      2 * n * d * Real.exp (-r ^ 2 / 2) + Real.exp (-B - 1) := by sorry

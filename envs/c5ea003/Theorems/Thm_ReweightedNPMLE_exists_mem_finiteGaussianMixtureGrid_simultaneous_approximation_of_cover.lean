-- Prove2me | Theorems.Thm_ReweightedNPMLE_exists_mem_finiteGaussianMixtureGrid_simultaneous_approximation_of_cover
-- name    : ReweightedNPMLE.exists_mem_finiteGaussianMixtureGrid_simultaneous_approximation_of_cover
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:44:41.00231+00:00
-- url     : https://prove2.me/theorems/5dae9aa3-54e3-41b5-95c7-9a5ad397a1fc
-- title:
--   A finite Gaussian mixture grid with simultaneous Hellinger and log-density control
-- statement:
--   Let $d,L\ge0$ and $M\ge1$ be integers. Let $\mu$ be a probability measure on a measurable space $\Theta$, and let $\vartheta:\Theta\to\mathbb R^d$ be measurable. Suppose its image lies in a nonempty compact set $K$, with $\|u\|\le S$ for all $u\in K$, where $S\ge0$. Let $X\subseteq\mathbb R^d$ satisfy $\|x\|\le T$ for all $x\in X$, with $T\ge0$. Let $Q\subseteq K$ be a finite internal $\varepsilon$-cover of $K$, where $\varepsilon>0$.
--
--   Write $f(x)=\int\varphi_d(x-\vartheta(a))\,d\mu(a)$ and define
--   $$
--   N=\binom{2L+d}{d},\quad \eta=\frac{2N}{M},\quad B=TS+\frac{S^2}{2},\quad
--   R=2e^{2B}\frac{B^{L+1}}{(L+1)!},\quad
--   H=\left(4e^{S^2}\frac{(S^2)^{2L+1}}{(2L+1)!}\right)^{1/2}.
--   $$
--   Assume $R\le1/2$ and $e^{2B}\eta\le1/2$. Then the finite grid of $(N+1)$-component Gaussian mixtures with locations in $Q$ and nonnegative denominator-$M$ simplex weights contains a density $p$ such that
--   $$
--   h^2(f,p)\le2H+\varepsilon^2+4\eta,
--   $$
--   and, simultaneously for every $x\in X$,
--   $$
--   |\log p(x)-\log f(x)|
--   \le(T+S)\varepsilon+2e^{2B}\eta+2R.
--   $$
--   Here $h^2(f,p)=\int_{\mathbb R^d}(\sqrt f-\sqrt p)^2\,dx$; zero component weights are allowed.
--
--   This deterministic construction supplies a concrete finite family controlling both global density error and local likelihood approximation, which is the basis for finite-net risk bounds.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianFiniteNet.lean#L254-L337

import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
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
import Mathlib.MeasureTheory.Integral.Bochner.L1
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Order.Compact
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_GaussianFiniteNet
import Definitions.Def_ReweightedNPMLE_GaussianMixtureHellinger
import Definitions.Def_ReweightedNPMLE_GaussianMixtureMeasure
import Definitions.Def_ReweightedNPMLE_Hellinger
import Definitions.Def_ReweightedNPMLE_PolynomialMoments
import Definitions.Def_ReweightedNPMLE_SimplexGrid
import Definitions.Def_ReweightedNPMLE_Weights

/-!
# Finite Gaussian-mixture grids

This module combines a finite location set with the denominator simplex grid.
It produces an actual finite set of Gaussian-mixture densities, proves the
entropy count used in the likelihood-net argument, and packages the local
log-density and global Hellinger rounding estimates for members of that set.
-/

open scoped BigOperators
open MeasureTheory

open ReweightedNPMLE

theorem ReweightedNPMLE.exists_mem_finiteGaussianMixtureGrid_simultaneous_approximation_of_cover
    {d L M : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : Measure Θ) [IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (K X : Set (Point d)) (Q : Finset (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hϑK : ∀ a, ϑ a ∈ K)
    {T S ε : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (hXbound : ∀ x ∈ X, ‖x‖ ≤ T)
    (hQK : ↑Q ⊆ K)
    (hQcover : ∀ u ∈ K, ∃ v ∈ Q, ‖u - v‖ ≤ ε)
    (hM : 0 < M)
    (hrelativeHalf : gaussianMomentRelativeError T S L ≤ 1 / 2)
    (hweightSmall : Real.exp (2 * (T * S + S ^ 2 / 2)) *
      (2 * gaussianMomentDimension d L / M) ≤ 1 / 2) :
    ∃ p ∈ finiteGaussianMixtureGrid d (gaussianMomentDimension d L) M Q,
      hellingerSq volume (gaussianMixture μ ϑ) p ≤
          2 * gaussianMomentHellingerError S L + ε ^ 2 +
            4 * (2 * gaussianMomentDimension d L / M) ∧
      ∀ x ∈ X,
        |Real.log (p x) - Real.log (gaussianMixture μ ϑ x)| ≤
          (T + S) * ε +
            2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
              (2 * gaussianMomentDimension d L / M) +
            2 * gaussianMomentRelativeError T S L := by sorry

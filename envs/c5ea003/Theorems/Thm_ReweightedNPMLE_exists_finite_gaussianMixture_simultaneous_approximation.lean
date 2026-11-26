-- Prove2me | Theorems.Thm_ReweightedNPMLE_exists_finite_gaussianMixture_simultaneous_approximation
-- name    : ReweightedNPMLE.exists_finite_gaussianMixture_simultaneous_approximation
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:44:17.779044+00:00
-- url     : https://prove2.me/theorems/c0e4be04-6bb5-4d1d-aeb2-f2b0bd55aed6
-- title:
--   One finite Gaussian mixture approximates both Hellinger distance and local likelihood
-- statement:
--   Let \(\mu\) be a probability measure and \(\vartheta:\Theta\to\mathbb R^d\) measurable, with every \(\vartheta(a)\) in a nonempty compact set \(K\). Suppose \(K\subseteq\{u:\|u\|\le S\}\), \(X\subseteq\{x:\|x\|\le T\}\), and \(S,T\ge0\). For every \(L\in\mathbb N\), there are probability weights and locations \(z_i\in K\), using at most \(N=\binom{2L+d}{d}+1\) atoms, such that, writing \(p=\int\phi_d(\,\cdot-\vartheta(a))d\mu(a)\), \(q=\sum_iw_i\phi_d(\,\cdot-z_i)\), and \(B=TS+S^2/2\),
--   \[
--   H^2(p,q)\le
--   \left(\frac{4e^{S^2}(S^2)^{2L+1}}{(2L+1)!}\right)^{1/2},
--   \qquad
--   \forall x\in X,\quad
--   \left|\frac{q(x)}{p(x)}-1\right|
--   \le\frac{2e^{2B}B^{L+1}}{(L+1)!}.
--   \]
--   Here \(\phi_d\) is the standard Gaussian density and \(H^2(p,q)=\int(\sqrt p-\sqrt q)^2dx\).
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/GaussianMixtureNet.lean#L435-L581

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

theorem ReweightedNPMLE.exists_finite_gaussianMixture_simultaneous_approximation
    {d L : ℕ} {Θ : Type*} [MeasurableSpace Θ]
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (ϑ : Θ → Point d) (hϑmeas : Measurable ϑ)
    (K X : Set (Point d))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hϑK : ∀ a, ϑ a ∈ K)
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (hXbound : ∀ x ∈ X, ‖x‖ ≤ T) :
    ∃ (w : Fin (Module.finrank ℝ
          (MonomialCoord d (2 * L) → ℝ) + 1) → ℝ)
      (z : Fin (Module.finrank ℝ
          (MonomialCoord d (2 * L) → ℝ) + 1) → Point d),
      w ∈ stdSimplex ℝ
        (Fin (Module.finrank ℝ (MonomialCoord d (2 * L) → ℝ) + 1)) ∧
      (∀ i, z i ∈ K) ∧
      hellingerSq MeasureTheory.volume (gaussianMixture μ ϑ)
          (finiteGaussianMixture w z) ≤
        (4 * (Real.exp (S ^ 2) * (S ^ 2) ^ (2 * L + 1) /
          (2 * L + 1).factorial)) ^ (1 / 2 : ℝ) ∧
      ∀ x ∈ X,
        |finiteGaussianMixture w z x / gaussianMixture μ ϑ x - 1| ≤
          2 * Real.exp (2 * (T * S + S ^ 2 / 2)) *
            ((T * S + S ^ 2 / 2) ^ (L + 1) / (L + 1).factorial) := by sorry

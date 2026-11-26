-- Prove2me | Theorems.Thm_ReweightedNPMLE_exists_finite_monomial_moment_matching
-- name    : ReweightedNPMLE.exists_finite_monomial_moment_matching
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:40:17.344586+00:00
-- url     : https://prove2.me/theorems/bb148d4c-6767-4a78-8bbc-ac7a5c01d994
-- title:
--   Exact compact-support moment matching with finitely many atoms
-- statement:
--   For integers $d,D\ge0$, let $\mathcal I_{d,D}=\{m\in\mathbb N^d:\sum_jm_j\le D\}$ and let
--   $$
--   \Phi_D(z)=(z^m)_{m\in\mathcal I_{d,D}},\qquad z^m=\prod_{j=1}^d z_j^{m_j}.
--   $$
--   Thus $\Phi_D$ contains every monomial of total degree at most $D$, including the constant monomial.
--
--   Let $\mu$ be a probability measure on a measurable space $\Theta$, and let $\theta:\Theta\to\mathbb R^d$ be a map. Suppose $K\subseteq\mathbb R^d$ is nonempty and compact, $\theta(a)\in K$ for $\mu$-almost every $a$, and $\Phi_D\circ\theta$ is integrable. Put $N=\binom{D+d}{d}$.
--
--   There exist points $z_1,\ldots,z_{N+1}\in K$ and weights $w_i\ge0$ with $\sum_iw_i=1$ such that
--   $$
--   \sum_{i=1}^{N+1}w_i\Phi_D(z_i)=\int_\Theta\Phi_D(\theta(a))\,d\mu(a).
--   $$
--   Equivalently, every moment of total degree at most $D$ agrees. Zero weights are permitted, so the conclusion includes representations with fewer atoms.
--
--   This finite representation is the deterministic moment-matching step in the Gaussian mixture approximation argument. The stated integrability assumption, rather than a separate measurability assumption on $\theta$, is what the formal theorem requires.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/PolynomialMoments.lean#L83-L117

import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_CompactConvexHull
import Definitions.Def_ReweightedNPMLE_Gaussian
import Definitions.Def_ReweightedNPMLE_PolynomialMoments

open ReweightedNPMLE

open scoped BigOperators
open Finset Fintype

theorem ReweightedNPMLE.exists_finite_monomial_moment_matching
    {Θ : Type*} [MeasurableSpace Θ] {d D : ℕ}
    (μ : MeasureTheory.Measure Θ) [MeasureTheory.IsProbabilityMeasure μ]
    (θ : Θ → Fin d → ℝ) (K : Set (Fin d → ℝ))
    (hKcompact : IsCompact K) (hKnonempty : K.Nonempty)
    (hθK : ∀ᵐ a ∂μ, θ a ∈ K)
    (hint : MeasureTheory.Integrable (fun a ↦ monomialFeature d D (θ a)) μ) :
    ∃ (w : Fin (Module.finrank ℝ (MonomialCoord d D → ℝ) + 1) → ℝ)
      (θ' : Fin (Module.finrank ℝ (MonomialCoord d D → ℝ) + 1) → Fin d → ℝ),
      w ∈ stdSimplex ℝ
        (Fin (Module.finrank ℝ (MonomialCoord d D → ℝ) + 1)) ∧
      (∀ i, θ' i ∈ K) ∧
        ∑ i, w i • monomialFeature d D (θ' i) =
          ∫ a, monomialFeature d D (θ a) ∂μ := by sorry

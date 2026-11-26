-- Prove2me | Theorems.Thm_ReweightedNPMLE_IsMonomialCombination_weighted_sum_eq_integral
-- name    : ReweightedNPMLE.IsMonomialCombination.weighted_sum_eq_integral
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:35:53.833845+00:00
-- url     : https://prove2.me/theorems/5bd15689-30b3-4f6c-a206-0e30a2016c4a
-- title:
--   Moment matching preserves all represented polynomial averages
-- statement:
--   For integers $d,D\ge0$, let $\mathcal I_{d,D}=\{m\in\mathbb N^d:\sum_jm_j\le D\}$ and let
--   $$
--   \Phi_D(z)=(z^m)_{m\in\mathcal I_{d,D}},\qquad z^m=\prod_{j=1}^d z_j^{m_j}.
--   $$
--   Thus $\Phi_D$ contains every monomial of total degree at most $D$, including the constant monomial.
--
--   Let $\mu$ be a measure on a measurable space $\Theta$, let $\theta:\Theta\to\mathbb R^d$, and assume $\Phi_D\circ\theta$ is integrable. Let $I$ be any finite index set, with arbitrary real weights $(w_i)_{i\in I}$ and points $(z_i)_{i\in I}\subseteq\mathbb R^d$. Suppose
--   $$
--   \sum_{i\in I}w_i\Phi_D(z_i)=\int_\Theta\Phi_D(\theta(a))\,d\mu(a).
--   $$
--   For every $f$ that is a linear combination of the degree-at-most-$D$ monomial coordinates,
--   $$
--   \sum_{i\in I}w_i f(z_i)=\int_\Theta f(\theta(a))\,d\mu(a).
--   $$
--   The weights need not be nonnegative or normalized, and $\mu$ need not be a probability measure.
--
--   The lemma upgrades coordinate moment matching to exact agreement for an entire finite-dimensional polynomial family.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/PolynomialMoments.lean#L194-L229

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

theorem ReweightedNPMLE.IsMonomialCombination.weighted_sum_eq_integral
    {Θ : Type*} [MeasurableSpace Θ] {d D : ℕ}
    {f : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (d := d) (D := D) f)
    {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (z : ι → Fin d → ℝ)
    (μ : MeasureTheory.Measure Θ) (θ : Θ → Fin d → ℝ)
    (hint : MeasureTheory.Integrable (fun a ↦ monomialFeature d D (θ a)) μ)
    (hmom : ∑ i, w i • monomialFeature d D (z i) =
      ∫ a, monomialFeature d D (θ a) ∂μ) :
    ∑ i, w i * f (z i) = ∫ a, f (θ a) ∂μ := by sorry

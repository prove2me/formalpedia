-- Prove2me | Theorems.Thm_ReweightedNPMLE_IsMonomialCombination_integrable_comp_of_feature
-- name    : ReweightedNPMLE.IsMonomialCombination.integrable_comp_of_feature
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:36:10.781133+00:00
-- url     : https://prove2.me/theorems/ec9922fa-bb9b-4b30-a029-6227d3d852db
-- title:
--   Integrability of polynomials from integrability of their feature vector
-- statement:
--   For integers $d,D\ge0$, let $\mathcal I_{d,D}=\{m\in\mathbb N^d:\sum_jm_j\le D\}$ and let
--   $$
--   \Phi_D(z)=(z^m)_{m\in\mathcal I_{d,D}},\qquad z^m=\prod_{j=1}^d z_j^{m_j}.
--   $$
--   Thus $\Phi_D$ contains every monomial of total degree at most $D$, including the constant monomial.
--
--   Let $\mu$ be any measure on a measurable space $\Theta$, let $\theta:\Theta\to\mathbb R^d$, and suppose $\Phi_D\circ\theta$ is integrable. If $f:\mathbb R^d\to\mathbb R$ is a linear combination of the coordinates of $\Phi_D$, then
--   $$
--   f\circ\theta\in L^1(\mu).
--   $$
--   No probability normalization of $\mu$ is assumed.
--
--   This allows finite-feature integrability to be reused for every polynomial represented by those features, including the truncated Gaussian exponential.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/PolynomialMoments.lean#L231-L251

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

theorem ReweightedNPMLE.IsMonomialCombination.integrable_comp_of_feature
    {Θ : Type*} [MeasurableSpace Θ] {d D : ℕ}
    {f : (Fin d → ℝ) → ℝ}
    (hf : IsMonomialCombination (d := d) (D := D) f)
    (μ : MeasureTheory.Measure Θ) (θ : Θ → Fin d → ℝ)
    (hint : MeasureTheory.Integrable (fun a ↦ monomialFeature d D (θ a)) μ) :
    MeasureTheory.Integrable (fun a ↦ f (θ a)) μ := by sorry

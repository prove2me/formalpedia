-- Prove2me | Theorems.Thm_ReweightedNPMLE_continuous_monomialFeature
-- name    : ReweightedNPMLE.continuous_monomialFeature
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:39:37.403459+00:00
-- url     : https://prove2.me/theorems/d6532638-f943-45e5-8c09-5699c612562c
-- title:
--   Continuity of the finite monomial feature map
-- statement:
--   For integers $d,D\ge0$, let $\mathcal I_{d,D}=\{m\in\mathbb N^d:\sum_jm_j\le D\}$ and let
--   $$
--   \Phi_D(z)=(z^m)_{m\in\mathcal I_{d,D}},\qquad z^m=\prod_{j=1}^d z_j^{m_j}.
--   $$
--   Thus $\Phi_D$ contains every monomial of total degree at most $D$, including the constant monomial.
--
--   The map
--   $$
--   \Phi_D:\mathbb R^d\longrightarrow\mathbb R^{\mathcal I_{d,D}}
--   $$
--   is continuous for every $d,D\ge0$.
--
--   Continuity makes compactly supported moment vectors amenable to convex-hull and finite-support representation arguments.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/PolynomialMoments.lean#L44-L60

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

theorem ReweightedNPMLE.continuous_monomialFeature (d D : ℕ) :
    Continuous (monomialFeature d D) := by sorry

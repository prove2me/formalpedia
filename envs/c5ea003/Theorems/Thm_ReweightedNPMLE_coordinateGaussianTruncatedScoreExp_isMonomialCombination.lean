-- Prove2me | Theorems.Thm_ReweightedNPMLE_coordinateGaussianTruncatedScoreExp_isMonomialCombination
-- name    : ReweightedNPMLE.coordinateGaussianTruncatedScoreExp_isMonomialCombination
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:40:22.856265+00:00
-- url     : https://prove2.me/theorems/9fc8f24d-552f-40a5-bc54-6b23a1b1d2f2
-- title:
--   The truncated Gaussian exponential uses moments through degree twice the order
-- statement:
--   For an integer $d\ge0$ and vectors $x,z\in\mathbb R^d$, define the Gaussian score
--   $$
--   s_x(z)=\sum_{j=1}^d x_jz_j-\frac12\sum_{j=1}^d z_j^2.
--   $$
--
--   For every integer $L\ge0$ and fixed $x\in\mathbb R^d$, define
--   $$
--   T_{L,x}(z)=\sum_{\ell=0}^L\frac{s_x(z)^\ell}{\ell!}.
--   $$
--   Then $T_{L,x}$ is a linear combination of monomials of total degree at most $2L$:
--   $$
--   T_{L,x}(z)=\sum_{|m|\le2L}c_m(L,x)z^m.
--   $$
--
--   Consequently, matching moments through degree $2L$ exactly matches the truncated exponential score, leaving only Taylor remainders to control.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/PolynomialMoments.lean#L536-L559

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

theorem ReweightedNPMLE.coordinateGaussianTruncatedScoreExp_isMonomialCombination {d : ℕ}
    (L : ℕ) (x : Fin d → ℝ) :
    IsMonomialCombination (d := d) (D := 2 * L)
      (coordinateGaussianTruncatedScoreExp L x) := by sorry

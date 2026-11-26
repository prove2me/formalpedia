-- Prove2me | Theorems.Thm_ReweightedNPMLE_relative_error_of_exp_lower_bound
-- name    : ReweightedNPMLE.relative_error_of_exp_lower_bound
-- status  : Proved
-- author  : @Hansheng Jiang
-- created : 2026-11-26T03:41:01.836357+00:00
-- url     : https://prove2.me/theorems/f6b6bc8f-62b6-4ccf-a659-b8f103c7fe65
-- title:
--   From absolute exponential error to a relative error bound
-- statement:
--   Let $a,b,B,r\in\mathbb R$ satisfy
--   $$
--   e^{-B}\le b,\qquad |a-b|\le2e^B r.
--   $$
--   Then
--   $$
--   \left|\frac ab-1\right|\le2e^{2B}r.
--   $$
--   No separate sign assumptions on $B$ or $r$ are imposed: the lower bound makes $b$ positive, and the error inequality itself forces $r\ge0$.
--
--   This elementary inequality converts an absolute Taylor approximation bound into the relative-density error needed for logarithmic likelihood control.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/PolynomialMoments.lean#L684-L703

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

theorem ReweightedNPMLE.relative_error_of_exp_lower_bound {a b B r : ℝ}
    (hlower : Real.exp (-B) ≤ b)
    (herror : |a - b| ≤ 2 * Real.exp B * r) :
    |a / b - 1| ≤ 2 * Real.exp (2 * B) * r := by sorry

-- Prove2me | Theorems.Thm_ReweightedNPMLE_norm_sub_lt_of_boundedLocationCellCode_eq
-- name    : ReweightedNPMLE.norm_sub_lt_of_boundedLocationCellCode_eq
-- status  : Proved
-- author  : @hansheng.jiang
-- created : 2026-11-26T03:42:08.806408+00:00
-- url     : https://prove2.me/theorems/e7b578ca-cc9b-4c29-856c-df0c1e9abdb0
-- title:
--   Equal coordinate-cell codes imply strict Euclidean proximity
-- statement:
--   Let $K\subset\mathbb R^d$ satisfy $\|u\|_2\le S$ for all $u\in K$, and let $\varepsilon>0$. Set $h=\varepsilon/(d+2)$ and encode a point by
--   $$c_i(u)=\left\lfloor\frac{u_i+S}{h}\right\rfloor,\qquad i=1,\ldots,d.$$
--   If $u,v\in K$ have the same code in every coordinate, then $\|u-v\|_2<\varepsilon$. The shifted coordinates are nonnegative, so the natural-number cell codes agree with the usual floor values. The strict estimate also holds in dimension zero.
-- source:
--   https://github.com/hanshengjiang/reweighted-npmle-lean/blob/5af8d16822c5a8a3f032b13eb95daea40f307484/ReweightedNPMLE/EuclideanLocationNet.lean#L68-L141

import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Definitions.Def_ReweightedNPMLE_EuclideanLocationNet
import Definitions.Def_ReweightedNPMLE_Gaussian

/-!
# Explicit finite nets for bounded Euclidean sets

This module implements the coordinate-cell construction used in the paper's
entropy argument.  A set contained in the radius-`S` Euclidean ball is split
into cells of coordinate width `ε / (d + 2)`.  Choosing one point of the set
from each occupied cell gives an internal `ε`-net with an explicit cardinality
bound.
-/

open scoped BigOperators

open ReweightedNPMLE

theorem ReweightedNPMLE.norm_sub_lt_of_boundedLocationCellCode_eq
    {d : ℕ} {K : Set (Point d)} {S ε : ℝ} (hε : 0 < ε)
    (hKbound : ∀ u ∈ K, ‖u‖ ≤ S) (u v : K)
    (hcode : boundedLocationCellCode S ε hε hKbound u =
      boundedLocationCellCode S ε hε hKbound v) :
    ‖(u : Point d) - (v : Point d)‖ < ε := by sorry

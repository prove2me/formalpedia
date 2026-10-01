-- Prove2me | Theorems.Thm_List_abs_foldr_max_apply_sub_le
-- name    : List.abs_foldr_max_apply_sub_le
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T17:32:34.480228+00:00
-- url     : https://prove2.me/theorems/3e29076b-e20d-4f03-b5d7-72a760909393
-- title:
--   Folded maxima are Lipschitz in the point
-- statement:
--   Pointwise maxima version of the Lipschitz envelope estimate.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/FiniteEnvelope.lean#L23-L26

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.MinMax
import Mathlib.Tactic
open Filter Topology

namespace List

open Filter Topology

theorem abs_foldr_max_apply_sub_le (l : List (ℝ → ℝ)) (r L x z : ℝ) (hL : 0 ≤ L)
    (hl : ∀ f ∈ l, |f x - f z| ≤ L * |x - z|) :
    |l.foldr (fun f s ↦ max (f x) s) r -
        l.foldr (fun f s ↦ max (f z) s) r| ≤ L * |x - z| := by sorry

end List

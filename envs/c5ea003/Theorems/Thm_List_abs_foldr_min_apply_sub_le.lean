-- Prove2me | Theorems.Thm_List_abs_foldr_min_apply_sub_le
-- name    : List.abs_foldr_min_apply_sub_le
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T17:32:15.394986+00:00
-- url     : https://prove2.me/theorems/9491f92b-cd8c-47cb-b0b6-90766e32e6f8
-- title:
--   Folded minima are Lipschitz in the point
-- statement:
--   Pointwise minima over a finite Lipschitz family are Lipschitz. Keyword lemma to theorem.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/FiniteEnvelope.lean#L11-L14

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.MinMax
import Mathlib.Tactic
open Filter Topology

namespace List

open Filter Topology

theorem abs_foldr_min_apply_sub_le (l : List (ℝ → ℝ)) (r L x z : ℝ) (hL : 0 ≤ L)
    (hl : ∀ f ∈ l, |f x - f z| ≤ L * |x - z|) :
    |l.foldr (fun f s ↦ min (f x) s) r -
        l.foldr (fun f s ↦ min (f z) s) r| ≤ L * |x - z| := by sorry

end List

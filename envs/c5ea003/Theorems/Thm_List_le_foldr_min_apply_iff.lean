-- Prove2me | Theorems.Thm_List_le_foldr_min_apply_iff
-- name    : List.le_foldr_min_apply_iff
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T17:32:22.60124+00:00
-- url     : https://prove2.me/theorems/b08c575f-8884-4d6c-af77-5548bc25ae52
-- title:
--   Lower bounds of folded minima split
-- statement:
--   y bounds the folded min iff it bounds r and every value.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/FiniteEnvelope.lean#L35-L37

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.MinMax
import Mathlib.Tactic
open Filter Topology

namespace List

open Filter Topology

theorem le_foldr_min_apply_iff (l : List (ℝ → ℝ)) (r x y : ℝ) :
    y ≤ l.foldr (fun f s ↦ min (f x) s) r ↔ y ≤ r ∧ ∀ f ∈ l, y ≤ f x := by sorry

end List

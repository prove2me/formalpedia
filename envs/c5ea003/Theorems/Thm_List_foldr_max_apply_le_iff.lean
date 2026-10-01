-- Prove2me | Theorems.Thm_List_foldr_max_apply_le_iff
-- name    : List.foldr_max_apply_le_iff
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-09-30T17:32:46.051048+00:00
-- url     : https://prove2.me/theorems/7d3275aa-b079-42f8-b6b2-72167bb9744c
-- title:
--   Upper bounds of folded maxima split
-- statement:
--   Dual characterization for folded maxima.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Analysis/FiniteEnvelope.lean#L41-L43

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.List.MinMax
import Mathlib.Tactic
open Filter Topology

namespace List

open Filter Topology

theorem foldr_max_apply_le_iff (l : List (ℝ → ℝ)) (r x y : ℝ) :
    l.foldr (fun f s ↦ max (f x) s) r ≤ y ↔ r ≤ y ∧ ∀ f ∈ l, f x ≤ y := by sorry

end List

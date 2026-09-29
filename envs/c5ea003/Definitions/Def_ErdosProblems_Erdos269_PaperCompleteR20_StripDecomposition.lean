-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_StripDecomposition
-- name    : ErdosProblems_Erdos269_PaperCompleteR20_StripDecomposition
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:11:49.705353+00:00
-- url     : https://prove2.me/theorems/19996442-fa76-4c67-8a5d-920c87f14a34
-- title:
--   StripDecomposition
-- statement:
--   Defines first-entry strips of a sequence of finite sets: the initial set at zero and the newly entered points T(n+1)\T(n) thereafter.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/StripDecomposition.lean#L1-L72
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# First-entry strips in a nested finite family

A point contributes to every later set after its first appearance. This
finite identity separates cancellation in the common interior from the
three moving boundary strips of a cubic difference.
-/

namespace ErdosProblems.Erdos269.PaperCompleteR20

open scoped BigOperators

def entryStrip {α : Type*} [DecidableEq α] (T : ℕ → Finset α) : ℕ → Finset α
  | 0 => T 0
  | n + 1 => T (n + 1) \ T n








end ErdosProblems.Erdos269.PaperCompleteR20



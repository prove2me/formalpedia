-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_divisorMajorantCost_one
-- name    : ErdosProblems.Erdos257.divisorMajorantCost_one
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T23:26:55.609413+00:00
-- url     : https://prove2.me/theorems/badaade9-d073-424b-a82d-ae454d0a8cfc
-- title:
--   Unit divisor-majorant cost is a reciprocal sum
-- statement:
--   With unit coefficients, divisorMajorantCost of a finite set E is the sum of 1/a over E.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/CoverIndependentPeriodicMean.lean#L104-L109
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

import Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
import Mathlib

/-!
# Cover-independent periodic means

Lemma A.1 of the 2026-09-06 Type B revision return: a nonnegative divisor
majorant of `g` controls every Cesàro average of `g`, hence every periodic
mean. This is not an irrationality theorem. It bounds cover cost.

The coprime-cover obstruction (Type B Theorem B.1) uses this averaging plus
the elementary density `1 - ∏(1 - 1/a)`; that density identity is recorded
as an ordinary proof in `VariableExponentCoverSeparation.md`.
-/


open Finset

open ErdosProblems.Erdos257

theorem ErdosProblems.Erdos257.divisorMajorantCost_one (E : Finset ℕ) :
    divisorMajorantCost E (fun _ => (1 : ℝ)) = ∑ a ∈ E, (1 : ℝ) / a := by sorry

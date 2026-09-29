-- Prove2me | Theorems.Thm_ErdosProblems_Erdos257_cesaro_le_divisorMajorantCost
-- name    : ErdosProblems.Erdos257.cesaro_le_divisorMajorantCost
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-24T22:07:21.605301+00:00
-- url     : https://prove2.me/theorems/838c4843-74a4-4016-a3a7-78d57bf92501
-- title:
--   Finite divisor majorant bounds a Cesàro average
-- statement:
--   If nonnegative g on positive integers is pointwise bounded by a nonnegative weighted sum over the divisors in finite positive D, then its average over 1,…,X (X>0) is at most divisorMajorantCost D c.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/CoverIndependentPeriodicMean.lean#L49-L102
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

theorem ErdosProblems.Erdos257.cesaro_le_divisorMajorantCost
    (g : ℕ → ℝ) (D : Finset ℕ) (c : ℕ → ℝ) (X : ℕ)
    (hX : 0 < X)
    (hD : ∀ d ∈ D, 0 < d)
    (hc : ∀ d ∈ D, 0 ≤ c d)
    (hg0 : ∀ n, 0 ≤ g n)
    (hmaj : ∀ n, 0 < n → g n ≤ ∑ d ∈ D.filter (fun d => d ∣ n), c d) :
    (∑ n ∈ Icc 1 X, g n) / X ≤ divisorMajorantCost D c := by sorry

-- Prove2me | Definitions.Def_ErdosProblems_Erdos257_CoverIndependentPeriodicMean
-- name    : ErdosProblems_Erdos257_CoverIndependentPeriodicMean
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-24T18:44:08.62974+00:00
-- url     : https://prove2.me/theorems/163e9705-e740-429c-9c6a-5cc14a849198
-- title:
--   Finite divisor-majorant cost
-- statement:
--   This bundle defines divisorMajorantCost(D,c) as the finite sum of c(d)/d over d in D.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/c93c2e4dd86a2e317e0cb650ea244fee1afd59c2/ErdosProblems/Erdos257/CoverIndependentPeriodicMean.lean#L1-L114
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L1-L75
--   Paper's authorship and AI-use disclosure: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/paper-house-style.sty#L180-L188
--   Erdős's earlier reciprocal-summable criterion is credited in the paper: https://github.com/wcook04/plectis-erdos/blob/6917e15ec4abc2623512254da93221e446eeb707/paper/257/erdos-257-mersenne-support-subseries.tex#L104-L110

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

namespace ErdosProblems.Erdos257

open Finset



/-- Cost of a finitely supported nonnegative divisor majorant. -/
noncomputable def divisorMajorantCost (D : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ d ∈ D, c d / d






end ErdosProblems.Erdos257



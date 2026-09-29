-- Prove2me | solution 1 for ErdosProblems.Erdos257.divisorMajorantCost_one
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T01:02:41.331133+00:00
-- url     : https://prove2.me/submissions/459c0a3f-2b8b-4779-aa44-1a4d7971b66f

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

namespace ErdosProblems.Erdos257
open Finset
end ErdosProblems.Erdos257

open Finset
open ErdosProblems in
open ErdosProblems.Erdos257 in
theorem solution (E : Finset ℕ) :
    divisorMajorantCost E (fun _ => (1 : ℝ)) = ∑ a ∈ E, (1 : ℝ) / a := by
  simp [divisorMajorantCost]

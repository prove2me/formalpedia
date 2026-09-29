-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
-- name    : ErdosProblems_Erdos243_LcmRecordCrossing
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:27:42.200111+00:00
-- url     : https://prove2.me/theorems/fc949424-f8cd-4566-bb50-59335daf4ede
-- title:
--   First crossing of a height
-- statement:
--   Defines FirstCrossing for a natural-valued sequence: the next state reaches a target height while every state through the current index remains below it. Existence and uniqueness of first crossings are separate theorem cards.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/LcmRecordCrossing.lean#L1-L314
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_LcmRecordCrossing is the versioned native alias of original module ErdosProblems.Erdos243.LcmRecordCrossing.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

namespace ErdosProblems.Erdos243.LcmRecordExcess
end ErdosProblems.Erdos243.LcmRecordExcess

/-!
# Counting the CRT heights crossed by one arithmetic step

The heights are the actual arithmetic progression `x + k * P`, not an
assumed cardinality bound. This supplies the finite local charging step in
the weighted-record argument of `LcmRecordExcess.md`. First-crossing existence,
uniqueness, and the finite partition across time require no monotonicity of
the numerator sequence. The existing CRT construction supplies the covering
from any finite family of sufficiently large pairwise-coprime old divisors.
Producing that family from an infinite canonical orbit and the analytic
divergence argument are not asserted by this module.
-/

namespace ErdosProblems.Erdos243.LcmRecordCrossing

open LcmRecordExcess







/-- The step ending at `U (n+1)` first reaches height `t`: every earlier
state, including its source, was strictly below that height. -/
def FirstCrossing (U : ℕ → ℕ) (t n : ℕ) : Prop :=
  (∀ j ≤ n, U j < t) ∧ t ≤ U (n + 1)

noncomputable instance (U : ℕ → ℕ) (t n : ℕ) : Decidable (FirstCrossing U t n) :=
  Classical.propDecidable _

















end ErdosProblems.Erdos243.LcmRecordCrossing



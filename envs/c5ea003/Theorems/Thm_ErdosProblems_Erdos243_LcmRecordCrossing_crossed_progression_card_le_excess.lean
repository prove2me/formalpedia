-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_crossed_progression_card_le_excess
-- name    : ErdosProblems.Erdos243.LcmRecordCrossing.crossed_progression_card_le_excess
-- status  : Open
-- author  : @willcook
-- created : 2026-09-27T22:49:58.441495+00:00
-- url     : https://prove2.me/theorems/fa890744-8b04-4d69-b7f5-7f9925ddace7
-- title:
--   Crossed CRT walls are paid for by jump excess
-- statement:
--   Let a finite set s index progression walls x+kP with P>B. Suppose every selected wall lies strictly above U and at most U+d, the exact feedback is d=(a−1)U−L, and each selected wall has a B-integer predecessor cover by divisors greater than B that divide L. Then |s|≤d−B.
-- source:
--   Pinned original Lean theorem and proof: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/LcmRecordCrossing.lean#L188-L211
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
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

namespace LcmRecordExcess
end LcmRecordExcess

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


open LcmRecordExcess

open ErdosProblems.Erdos243.LcmRecordCrossing

open ErdosProblems.Erdos243.LcmRecordExcess

theorem ErdosProblems.Erdos243.LcmRecordCrossing.crossed_progression_card_le_excess (s : Finset ℕ)
    (x P U d B : ℕ) (a L : ℤ) (hP : B < P)
    (hlo : ∀ k ∈ s, U < x + k * P)
    (hhi : ∀ k ∈ s, x + k * P ≤ U + d)
    (hfeedback : (d : ℤ) = (a - 1) * U - L)
    (hcover : ∀ k ∈ s, ∀ z : ℤ,
      (x + k * P : ℕ) - (B : ℤ) ≤ z → z < (x + k * P : ℕ) →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ L ∧ m ∣ z) :
    s.card ≤ d - B := by sorry

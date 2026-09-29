-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_not_summable_recordExcessWeight_of_progression
-- name    : ErdosProblems.Erdos243.LcmRecordCrossing.not_summable_recordExcessWeight_of_progression
-- status  : Open
-- author  : @willcook
-- created : 2026-09-27T23:00:39.135745+00:00
-- url     : https://prove2.me/theorems/f5058468-3b8b-4ec7-a3fe-053a25267275
-- title:
--   Nonsummable progression weights force record-charge divergence
-- statement:
--   Let U be an unbounded natural height sequence with U_0<x, and let P>B. Suppose every strict global-record step satisfies the exact integer feedback U_(n+1)−U_n=(a_n−1)U_n−L_n, and at every step n every B-integer predecessor block before x+kP is covered by divisors greater than B also dividing L_n. If f is nonnegative and antitone and Σ_k f(x+kP) diverges, then the series of recordExcessWeight(U,B,f) diverges, where its n-th term is (U_(n+1)−U_n−B)^+ f(U_n) at a strict global record and zero otherwise.
-- source:
--   Pinned original Lean theorem and proof: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/LcmRecordDivergence.lean#L20-L57
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordDivergence
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

/-!
# From finite first crossings to divergent record mass

This module transfers nonsummability of the actual progression weights to
the record-excess series. The sequence need only reach arbitrarily large
heights; no monotonicity or limit at infinity is assumed. The analytic input
that a particular weight has divergent progression sum remains explicit.
-/

open ErdosProblems.Erdos243.LcmRecordCrossing

theorem ErdosProblems.Erdos243.LcmRecordCrossing.not_summable_recordExcessWeight_of_progression
    (U : ℕ → ℕ) (a L : ℕ → ℤ) (x P B : ℕ) (hP : B < P)
    (hzero : U 0 < x)
    (hunbounded : ∀ t : ℕ, ∃ n, t ≤ U n)
    (hfeedback : ∀ n, (∀ j ≤ n, U j < U (n + 1)) →
      ((U (n + 1) - U n : ℕ) : ℤ) = (a n - 1) * U n - L n)
    (hcover : ∀ n k : ℕ, ∀ z : ℤ,
      (x + k * P : ℕ) - (B : ℤ) ≤ z → z < (x + k * P : ℕ) →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ L n ∧ m ∣ z)
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u)
    (hdiverges : ¬ Summable (fun k : ℕ => f (x + k * P))) :
    ¬ Summable (recordExcessWeight U B f) := by sorry

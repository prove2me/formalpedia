-- Prove2me | Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_finite_record_weighted_bound
-- name    : ErdosProblems.Erdos243.LcmRecordCrossing.finite_record_weighted_bound
-- status  : Open
-- author  : @willcook
-- created : 2026-09-27T22:58:37.235232+00:00
-- url     : https://prove2.me/theorems/30546b5d-00fb-41a4-aa42-68a4a4dd2b90
-- title:
--   Finite CRT wall weight is charged to genuine records
-- statement:
--   Let P>B and let s be a finite set of progression walls x+kP, each strictly above U_0 and reached by time N. Suppose that at every strict global-record step n<N the integer rise U_(n+1)−U_n equals (a_n−1)U_n−L_n, and at every n<N each selected wall has a B-integer predecessor cover by divisors greater than B that divide L_n. For a nonnegative antitone weight f on natural heights, Σ_(k∈s)f(x+kP) is at most Σ_(n<N) of the charge (U_(n+1)−U_n−B)^+ f(U_n) at strict records, with zero at nonrecords.
-- source:
--   Pinned original Lean theorem and proof: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/LcmRecordCrossing.lean#L235-L285
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

theorem ErdosProblems.Erdos243.LcmRecordCrossing.finite_record_weighted_bound (s : Finset ℕ) (U : ℕ → ℕ)
    (a L : ℕ → ℤ) (x P B N : ℕ) (hP : B < P)
    (hzero : ∀ k ∈ s, U 0 < x + k * P)
    (hN : ∀ k ∈ s, ∃ j ≤ N, x + k * P ≤ U j)
    (hfeedback : ∀ n < N, (∀ j ≤ n, U j < U (n + 1)) →
      ((U (n + 1) - U n : ℕ) : ℤ) = (a n - 1) * U n - L n)
    (hcover : ∀ n < N, ∀ k ∈ s, ∀ z : ℤ,
      (x + k * P : ℕ) - (B : ℤ) ≤ z → z < (x + k * P : ℕ) →
      ∃ m : ℤ, (B : ℤ) < m ∧ m ∣ L n ∧ m ∣ z)
    (f : ℕ → ℝ) (hf : Antitone f) (hpos : ∀ u, 0 ≤ f u) :
    ∑ k ∈ s, f (x + k * P) ≤
      ∑ n ∈ Finset.range N,
        if (∀ j ≤ n, U j < U (n + 1)) then
          ((U (n + 1) - U n - B : ℕ) : ℝ) * f (U n) else 0 := by sorry

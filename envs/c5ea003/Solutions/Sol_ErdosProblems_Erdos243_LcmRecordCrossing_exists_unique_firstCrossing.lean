-- Prove2me | solution 1 for ErdosProblems.Erdos243.LcmRecordCrossing.exists_unique_firstCrossing
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:53:58.196977+00:00
-- url     : https://prove2.me/submissions/b04e0a84-7695-40de-b366-3e6806ba5f3a

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

namespace ErdosProblems.Erdos243.LcmRecordCrossing
open LcmRecordExcess
end ErdosProblems.Erdos243.LcmRecordCrossing

open LcmRecordExcess
open ErdosProblems in
open ErdosProblems.Erdos243 in
open ErdosProblems.Erdos243.LcmRecordCrossing in
open ErdosProblems.Erdos243.LcmRecordExcess in
theorem solution (U : ℕ → ℕ) (t N : ℕ)
    (hzero : U 0 < t) (hN : ∃ j ≤ N, t ≤ U j) :
    ∃! n, n < N ∧ FirstCrossing U t n := by
  obtain ⟨j, hjN, hj⟩ := hN
  let reached : ∃ j, t ≤ U j := ⟨j, hj⟩
  have hreach := Nat.find_spec reached
  have hbound := Nat.find_min' reached hj
  have hpositive : 0 < Nat.find reached := by
    by_contra h
    have hzeroindex : Nat.find reached = 0 := by omega
    rw [hzeroindex] at hreach
    omega
  have hsucc : Nat.find reached - 1 + 1 = Nat.find reached := by omega
  have hfirst : FirstCrossing U t (Nat.find reached - 1) := by
    constructor
    · intro j hj
      have hnot := Nat.find_min reached (show j < Nat.find reached by omega)
      omega
    · simpa only [hsucc] using hreach
  refine ⟨Nat.find reached - 1, ⟨by omega, hfirst⟩, ?_⟩
  intro m hm
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hlow := hfirst.1 (m + 1) (by omega)
    have hhigh := hm.2.2
    omega
  · have hlow := hm.2.1 (Nat.find reached - 1 + 1) (by omega)
    have hhigh := hfirst.2
    omega

-- Prove2me | solution 1 for ErdosProblems.Erdos243.LcmRecordCrossing.crossed_progression_spacing
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T22:51:52.097658+00:00
-- url     : https://prove2.me/submissions/16047f45-a861-4197-a4b2-5cd6bd15c9ca

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
theorem solution (s : Finset ℕ) (hs : s.Nonempty)
    (x P U d : ℕ)
    (hlo : ∀ k ∈ s, U < x + k * P)
    (hhi : ∀ k ∈ s, x + k * P ≤ U + d) :
    (s.card - 1) * P < d := by
  have hsub : s ⊆ Finset.Icc (s.min' hs) (s.max' hs) := by
    intro k hk
    exact Finset.mem_Icc.mpr ⟨s.min'_le k hk, s.le_max' k hk⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hc
  have hminmax := s.min'_le_max' hs
  have hspan : s.card - 1 ≤ s.max' hs - s.min' hs := by omega
  have hmul := Nat.mul_le_mul_right P hspan
  have hsplit : s.max' hs = s.min' hs + (s.max' hs - s.min' hs) := by omega
  have hleft := hlo (s.min' hs) (s.min'_mem hs)
  have hright := hhi (s.max' hs) (s.max'_mem hs)
  rw [hsplit, Nat.add_mul] at hright
  omega

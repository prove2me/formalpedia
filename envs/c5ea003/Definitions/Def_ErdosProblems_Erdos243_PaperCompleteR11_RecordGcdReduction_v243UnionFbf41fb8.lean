-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_RecordGcdReduction_v243UnionFbf41fb8
-- name    : ErdosProblems_Erdos243_PaperCompleteR11_RecordGcdReduction_v243UnionFbf41fb8
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:53:37.947118+00:00
-- url     : https://prove2.me/theorems/60cb99d2-56e8-4d98-bde6-a75d98bf68a4
-- title:
--   Record-growth orbit and exact common-divisor quotient
-- statement:
--   Defines an orbit of positive natural multiplier a, height U and denominator D, with strictly increasing a, exact recurrences U_(n+1)+D_n=a_n U_n and D_(n+1)=a_n D_n, a lower binary-tower bound for a, an exponential upper bound for the running maximum of U, a shifted binary-tower upper bound for D, and unbounded U. For a positive common divisor of U_s and D_s at an attained record s, defines the shifted quotient orbit; included source proofs preserve the exact states and running maximum under that quotient. The no-record-cap contradiction is a separate theorem.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/PaperCompleteR11/RecordGcdReduction.lean#L1-L196
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_PaperCompleteR11_RecordGcdReduction_v243UnionFbf41fb8 is the versioned native alias of original module ErdosProblems.Erdos243.PaperCompleteR11.RecordGcdReduction.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Definitions.Def_ErdosProblems_Erdos243_GlobalLcmHeight
import Definitions.Def_ErdosProblems_Erdos243_CumulativeLcmTransfer
import Definitions.Def_ErdosProblems_Erdos243_LcmCriticalBoundary
import Definitions.Def_ErdosProblems_Erdos243_LcmRecordCrossing
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_Limits
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_RealTail_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_CanonicalState_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PrimitiveRecordBarrier
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_RecordDivisibility_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_ProductDefect_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR7_LcmDefect_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_GrowthRecordEquivalence_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CanonicalGrowthBounds_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_CoprimeCores_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_LogLogNormaliser_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_OrbitBlockArithmetic_v243UnionFbf41fb8
import Definitions.Def_ErdosProblems_Erdos243_PaperCompleteR11_PresievedCRT_v243UnionFbf41fb8
import Mathlib
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Defs
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Exact record-preserving quotient tails


The growth record below packages already derived orbit properties, not
any assertion about record gaps. Quotients are constructed from a genuine
common divisor. A global attained record is used as the starting index,
so the original running maximum is preserved exactly, including its prefix.
-/

namespace ErdosProblems.Erdos243.PaperCompleteR11

/-- Exact arithmetic and growth data used by both block arguments. -/
structure RecordGrowthOrbit : Type where
  a : ℕ → ℕ
  U : ℕ → ℕ
  D : ℕ → ℕ
  increasing : ∀ ⦃m n : ℕ⦄, m < n → a m < a n
  a_pos : ∀ n, 0 < a n
  U_pos : ∀ n, 0 < U n
  D_pos : ∀ n, 0 < D n
  U_step : ∀ n, U (n + 1) + D n = a n * U n
  D_step : ∀ n, D (n + 1) = a n * D n
  lower : ∃ N : ℕ, ∀ k, 2 * binaryTower k ≤ a (N + k)
  record_bound : ∃ K : ℕ, ∀ n, runningMax U n ≤ 2 ^ (K + n)
  den_bound : ∃ L : ℕ, ∀ n, D n ≤ binaryTower (n + L)
  unbounded : ∀ H : ℕ, ∃ n, H ≤ U n







/-- A quotient tail's running maximum is bounded by the actual global
maximum, without requiring the quotient itself to be monotone. -/
theorem runningMax_shift_div_le (U : ℕ → ℕ) (s g n : ℕ) :
    runningMax (fun j ↦ U (s + j) / g) n ≤ runningMax U (s + n) := by
  obtain ⟨j, hj, heq⟩ := runningMax_attained (fun j ↦ U (s + j) / g) n
  rw [← heq]
  exact (Nat.div_le_self _ _).trans (le_runningMax U (by omega))

/-- Common divisors persist in natural coordinates on the entire tail. -/
theorem RecordGrowthOrbit.common_divisor_tail (O : RecordGrowthOrbit)
    (s g : ℕ) (hUg : g ∣ O.U s) (hDg : g ∣ O.D s) :
    ∀ n, g ∣ O.U (s + n) ∧ g ∣ O.D (s + n) := by
  intro n
  induction n with
  | zero => simpa only [Nat.add_zero] using And.intro hUg hDg
  | succ n ih =>
      have hu := O.U_step (s + n)
      have hd := O.D_step (s + n)
      constructor
      · have hsum : g ∣ O.U (s + n + 1) + O.D (s + n) := by
          rw [hu]
          exact dvd_mul_of_dvd_right ih.1 _
        simpa only [Nat.add_assoc] using (Nat.dvd_add_iff_left ih.2).mpr hsum
      · rw [show s + (n + 1) = (s + n) + 1 by omega, hd]
        exact dvd_mul_of_dvd_right ih.2 _

/-- The exact quotient orbit, with every positivity and growth property
proved from the original orbit. -/
def RecordGrowthOrbit.quotientAt (O : RecordGrowthOrbit) (s g : ℕ)
    (hg : 0 < g) (hUg : g ∣ O.U s) (hDg : g ∣ O.D s) : RecordGrowthOrbit := by
  have hdiv := O.common_divisor_tail s g hUg hDg
  refine {
    a := fun n ↦ O.a (s + n)
    U := fun n ↦ O.U (s + n) / g
    D := fun n ↦ O.D (s + n) / g
    increasing := fun i j hij ↦ O.increasing (by omega)
    a_pos := fun n ↦ O.a_pos _
    U_pos := fun n ↦ Nat.div_pos (Nat.le_of_dvd (O.U_pos _) (hdiv n).1) hg
    D_pos := fun n ↦ Nat.div_pos (Nat.le_of_dvd (O.D_pos _) (hdiv n).2) hg
    U_step := ?_
    D_step := ?_
    lower := ?_
    record_bound := ?_
    den_bound := ?_
    unbounded := ?_ }
  · intro n
    apply Nat.eq_of_mul_eq_mul_left hg
    rw [Nat.mul_add, Nat.mul_div_cancel' (hdiv (n + 1)).1,
      Nat.mul_div_cancel' (hdiv n).2]
    calc
      O.U (s + (n + 1)) + O.D (s + n) = O.a (s + n) * O.U (s + n) := by
        simpa only [Nat.add_assoc] using O.U_step (s + n)
      _ = g * (O.a (s + n) * (O.U (s + n) / g)) := by
        rw [mul_left_comm, Nat.mul_div_cancel' (hdiv n).1]
  · intro n
    rw [show s + (n + 1) = (s + n) + 1 by omega, O.D_step]
    exact Nat.mul_div_assoc _ (hdiv n).2
  · obtain ⟨N, hN⟩ := O.lower
    refine ⟨N, fun k ↦ ?_⟩
    have hshift : O.a (N + k) ≤ O.a (s + (N + k)) := by
      by_cases hs : s = 0
      · simpa [hs]
      · exact Nat.le_of_lt (O.increasing (by omega))
    exact (hN k).trans hshift
  · obtain ⟨K, hK⟩ := O.record_bound
    refine ⟨K + s, fun n ↦ ?_⟩
    simpa only [Nat.add_assoc] using (runningMax_shift_div_le O.U s g n).trans (hK (s + n))
  · obtain ⟨L, hL⟩ := O.den_bound
    refine ⟨s + L, fun n ↦ ?_⟩
    have hh := (Nat.div_le_self (O.D (s + n)) g).trans (hL (s + n))
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hh
  · intro H
    obtain ⟨j, hj⟩ := O.unbounded (max (g * H) (runningMax O.U s + 1))
    have hjbig : runningMax O.U s < O.U j := by
      have hh := (le_max_right (g * H) (runningMax O.U s + 1)).trans hj
      omega
    have hsj : s ≤ j := by
      by_contra hnot
      have hh := le_runningMax O.U (show j ≤ s by omega)
      omega
    let n := j - s
    have hsn : s + n = j := Nat.add_sub_of_le hsj
    refine ⟨n, ?_⟩
    have hid : g * (O.U (s + n) / g) = O.U j := by
      rw [Nat.mul_div_cancel' (hdiv n).1, hsn]
    have hgh : g * H ≤ g * (O.U (s + n) / g) := by
      rw [hid]
      exact (le_max_left _ _).trans hj
    by_contra hnot
    have hlt := Nat.mul_lt_mul_of_pos_left (show O.U (s + n) / g < H by omega) hg
    omega





end ErdosProblems.Erdos243.PaperCompleteR11



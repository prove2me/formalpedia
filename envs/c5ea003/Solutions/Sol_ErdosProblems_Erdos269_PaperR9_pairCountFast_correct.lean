-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR9.pairCountFast_correct
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T19:19:07.608263+00:00
-- url     : https://prove2.me/submissions/3670c55c-cbc5-4206-8735-41204d9cab9f

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_PaperR9SourceCounts
import Theorems.Thm_ErdosProblems_Erdos269_PaperR9_mem_strictSmoothPairs_iff
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Exact source-count normalisation for certificate reconstruction

This module does not certify a generated list by fiat. It starts with the
library's actual strictSmoothPairs / strictSmoothExponents and proves the
one-dimensional pair count, cumulative pure-power count, threshold difference,
and complete ordered dyadic digit formula.

The executable pair evaluator uses successive division. It does not enumerate
a box of side `x` or compute real logarithms. Its boundary sweep is linear in the two exponent bounds. No unproved
logarithmic-interval or Euclidean floor-sum optimisation is used by this return.

Source APIs reused: RestrictedFloorSum.lean, strictSmoothShell_card,
restrictedPurePowerCount_eq_restrictedLogFloorSum, restrictedLogFloorSum_succ_sub;
Mathlib/Data/Nat/Log.lean; Lean src/Init/Data/Nat/Div/Basic.lean.
Finset.card_eq_sum_card_fiberwise is reused exactly as in the supplied
RestrictedFloorSum.lean:332.

-/

namespace ErdosProblems.Erdos269.PaperR9
open Finset
end ErdosProblems.Erdos269.PaperR9

open Finset
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR9 in
theorem solution {q r x : ℕ} (hq : 1 < q) (hr : 1 < r) :
    pairCountFast q r x = (strictSmoothPairs q r x).card := by
  classical
  by_cases hx : x ≤ 1
  · have hempty : strictSmoothPairs q r x = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro e he
      have he' := (mem_strictSmoothPairs_iff hq hr e).mp he
      have hp : 0 < q ^ e.1 * r ^ e.2 := by positivity
      omega
    simp [pairCountFast, hx, hempty]
  have hx1 : 1 < x := by omega
  have hN : x - 1 ≠ 0 := by omega
  let I := Nat.log q (x - 1)
  have hfirst : ∀ e ∈ strictSmoothPairs q r x, e.1 ≤ I := by
    intro e he
    have he' := (mem_strictSmoothPairs_iff hq hr e).mp he
    have hprod : 0 < q ^ e.1 * r ^ e.2 := by positivity
    have hpow := Nat.le_of_dvd hprod (show q ^ e.1 ∣ q ^ e.1 * r ^ e.2 from ⟨r ^ e.2, rfl⟩)
    apply Nat.le_log_of_pow_le hq
    omega
  have hquot : ∀ i ∈ range (I + 1), 0 < (x - 1) / q ^ i := by
    intro i hi
    have hi' : i ≤ I := by simpa only [mem_range, Nat.lt_succ_iff] using hi
    have hpow : q ^ i ≤ x - 1 := Nat.pow_le_of_le_log hN hi'
    exact Nat.div_pos hpow (by positivity)
  have hcard : (strictSmoothPairs q r x).card =
      ∑ i ∈ range (I + 1), ((strictSmoothPairs q r x).filter (fun e => e.1 = i)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro e he
    exact mem_range.mpr (Nat.lt_succ_of_le (hfirst e he))
  rw [pairCountFast, if_neg hx, hcard]
  change (∑ i ∈ range (I + 1), (Nat.log r ((x - 1) / q ^ i) + 1)) = _
  refine Finset.sum_congr (s₁ := range (I + 1)) (s₂ := range (I + 1))
    (f := fun i : ℕ => Nat.log r ((x - 1) / q ^ i) + 1)
    (g := fun i : ℕ => ((strictSmoothPairs q r x).filter (fun e => e.1 = i)).card) rfl ?_
  intro i hi
  have hQ := hquot i hi
  symm
  trans (range (Nat.log r ((x - 1) / q ^ i) + 1)).card
  · apply Finset.card_bij (fun e _ => e.2)
    · intro e he
      obtain ⟨he, hei⟩ := mem_filter.mp he
      have hv := (mem_strictSmoothPairs_iff hq hr e).mp he
      rw [hei] at hv
      have hvle : q ^ i * r ^ e.2 ≤ x - 1 := by omega
      have hmul : r ^ e.2 * q ^ i ≤ x - 1 := by simpa only [mul_comm] using hvle
      have hle : r ^ e.2 ≤ (x - 1) / q ^ i :=
        (Nat.le_div_iff_mul_le (by positivity : 0 < q ^ i)).mpr hmul
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_log_of_pow_le hr hle))
    · intro e he f hf hef
      have he' := (mem_filter.mp he).2
      have hf' := (mem_filter.mp hf).2
      exact Prod.ext (he'.trans hf'.symm) hef
    · intro j hj
      have hj' : j ≤ Nat.log r ((x - 1) / q ^ i) :=
        Nat.lt_succ_iff.mp (mem_range.mp hj)
      have hp : r ^ j ≤ (x - 1) / q ^ i := Nat.pow_le_of_le_log hQ.ne' hj'
      have hmul := (Nat.le_div_iff_mul_le (by positivity : 0 < q ^ i)).mp hp
      refine ⟨(i, j), mem_filter.mpr ⟨?_, rfl⟩, rfl⟩
      apply (mem_strictSmoothPairs_iff hq hr (i, j)).mpr
      dsimp only
      have hvle : q ^ i * r ^ j ≤ x - 1 := by simpa only [mul_comm] using hmul
      omega
  · simp

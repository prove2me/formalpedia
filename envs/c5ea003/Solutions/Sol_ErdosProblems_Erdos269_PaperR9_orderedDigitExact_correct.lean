-- Prove2me | solution 1 for ErdosProblems.Erdos269.PaperR9.orderedDigitExact_correct
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T20:00:40.937594+00:00
-- url     : https://prove2.me/submissions/c8732ae2-1309-4216-a6e3-7168b2ec89f7

import Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
import Definitions.Def_ErdosProblems_Erdos269_ThreePrimeRunningLcm
import Definitions.Def_ErdosProblems_Erdos269_RestrictedFloorSum
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockMassIdentity
import Definitions.Def_ErdosProblems_Erdos269_DyadicBlockThresholdPartition
import Definitions.Def_ErdosProblems_Erdos269_PaperR9SourceCounts
import Theorems.Thm_ErdosProblems_Erdos269_strictSmoothExponents_mono
import Theorems.Thm_ErdosProblems_Erdos269_strictSmoothShell_card
import Theorems.Thm_ErdosProblems_Erdos269_PaperR9_beforeThreshold_eq_prefix_sub
import Theorems.Thm_ErdosProblems_Erdos269_PaperR9_pairCountFast_correct
import Theorems.Thm_ErdosProblems_Erdos269_restrictedLogFloorSum_succ_sub
import Theorems.Thm_ErdosProblems_Erdos269_restrictedPurePowerCount_eq_restrictedLogFloorSum
import Theorems.Thm_ErdosProblems_Erdos269_smoothCountLT_swap_first_second
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









theorem pairCountDivLoop_eq_sum (q r k N : ℕ) :
    pairCountDivLoop q r k N =
      ∑ i ∈ range k, if N / q ^ i = 0 then 0 else Nat.log r (N / q ^ i) + 1 := by
  induction k generalizing N with
  | zero => simp [pairCountDivLoop]
  | succ k ih =>
      by_cases hN : N = 0
      · simp [pairCountDivLoop, hN]
      rw [pairCountDivLoop, if_neg hN, ih, Finset.sum_range_succ']
      simp only [pow_zero, Nat.div_one, if_neg hN]
      rw [Nat.add_comm (Nat.log r N + 1)]
      apply congrArg (fun z : ℕ => z + (Nat.log r N + 1))
      refine Finset.sum_congr rfl ?_
      intro i hi
      simp only [Nat.div_div_eq_div_mul, ← pow_succ']



theorem pairCountExact_correct {q r x : ℕ} (hq : 1 < q) (hr : 1 < r) :
    pairCountExact q r x = (strictSmoothPairs q r x).card := by
  rw [← pairCountFast_correct hq hr]
  by_cases hx : x ≤ 1
  · simp [pairCountExact, pairCountFast, hx]
  rw [pairCountExact, pairCountFast, if_neg hx, if_neg hx, pairCountDivLoop_eq_sum]
  refine Finset.sum_congr
    (s₁ := range (Nat.log q (x - 1) + 1)) (s₂ := range (Nat.log q (x - 1) + 1))
    (f := fun i : ℕ => if (x - 1) / q ^ i = 0 then (0 : ℕ) else Nat.log r ((x - 1) / q ^ i) + 1)
    (g := fun i : ℕ => Nat.log r ((x - 1) / q ^ i) + 1) rfl ?_
  intro i hi
  have hpow : q ^ i ≤ x - 1 := Nat.pow_le_of_le_log (by omega)
    (Nat.lt_succ_iff.mp (mem_range.mp hi))
  have hQ : 0 < (x - 1) / q ^ i := Nat.div_pos hpow (by positivity)
  dsimp only
  rw [if_neg hQ.ne']



theorem lowerPower_correct (r j N : ℕ) (hr : 1 < r) (hN : 0 < N)
    (hu : N < r ^ (j + 1)) :
    lowerPower r j (r ^ j) N = (Nat.log r N, r ^ Nat.log r N) := by
  revert hu
  induction j with
  | zero =>
      intro hu
      have hlog : Nat.log r N = 0 := Nat.log_of_lt (by simpa using hu)
      simp only [lowerPower, hlog]
  | succ j ih =>
      intro hu
      by_cases hp : r ^ (j + 1) ≤ N
      · have hlog : Nat.log r N = j + 1 := Nat.log_eq_of_pow_le_of_lt_pow hp hu
        simp only [lowerPower, if_pos hp, hlog]
      · have hdiv : r ^ (j + 1) / r = r ^ j := by
          rw [pow_succ', Nat.mul_div_cancel_left _ (by omega)]
        rw [lowerPower, if_neg hp, hdiv]
        exact ih (by omega)



theorem pairCountSweep_correct (q r k N j : ℕ) (hr : 1 < r)
    (hu : N < r ^ (j + 1)) :
    pairCountSweep q r k N j (r ^ j) = pairCountDivLoop q r k N := by
  revert hu
  induction k generalizing N j with
  | zero => intro hu; rfl
  | succ k ih =>
      intro hu
      by_cases hN : N = 0
      · simp [pairCountSweep, pairCountDivLoop, hN]
      rw [pairCountSweep, if_neg hN, lowerPower_correct r j N hr (by omega) hu,
        pairCountDivLoop, if_neg hN]
      dsimp only
      congr 1
      exact ih (N / q) (Nat.log r N)
        ((Nat.div_le_self N q).trans_lt (Nat.lt_pow_succ_log_self hr N))



theorem pairCountChecked_correct {q r x : ℕ} (hq : 1 < q) (hr : 1 < r) :
    pairCountChecked q r x = (strictSmoothPairs q r x).card := by
  rw [← pairCountExact_correct hq hr]
  by_cases hx : x ≤ 1
  · simp [pairCountChecked, pairCountExact, hx]
  rw [pairCountChecked, pairCountExact, if_neg hx, if_neg hx]
  dsimp only
  exact pairCountSweep_correct _ _ _ _ _ hr (Nat.lt_pow_succ_log_self hr _)



theorem purePrefixCount_correct {p q r : ℕ} (hp : 1 < p) (hq : 1 < q)
    (hr : 1 < r) (e : ℕ) :
    purePrefixCount p q r e = smoothCountLT p q r (p ^ e) := by
  have heq : ∀ a, smoothCountLT p q r (p ^ a) = restrictedLogFloorSum p q r a := by
    intro a
    exact restrictedPurePowerCount_eq_restrictedLogFloorSum p q r a hp (by omega) (by omega)
  induction e with
  | zero =>
      simp [purePrefixCount, smoothCountLT, strictSmoothExponents, smooth3Val,
        Nat.ne_of_gt (lt_trans Nat.zero_lt_one hp),
        Nat.ne_of_gt (lt_trans Nat.zero_lt_one hq),
        Nat.ne_of_gt (lt_trans Nat.zero_lt_one hr)]
  | succ e ih =>
      have hd := restrictedLogFloorSum_succ_sub p q r e hp hq hr
      rw [← heq (e + 1), ← heq e, ← pairCountChecked_correct hq hr] at hd
      have hle : smoothCountLT p q r (p ^ e) ≤ smoothCountLT p q r (p ^ (e + 1)) :=
        Finset.card_le_card (strictSmoothExponents_mono p q r
          (Nat.pow_le_pow_right (by omega) (Nat.le_succ e)))
      change (∑ k ∈ range (e + 1), pairCountChecked q r (p ^ (k + 1))) = _
      rw [sum_range_succ]
      change purePrefixCount p q r e + pairCountChecked q r (p ^ (e + 1)) = _
      rw [ih]
      omega

theorem smoothCountLT_swap_first_third (p q r x : ℕ) :
    smoothCountLT p q r x = smoothCountLT r q p x := by
  classical
  unfold smoothCountLT
  apply Finset.card_bij (fun z _ => (z.2.2, z.2.1, z.1))
  · intro z hz
    obtain ⟨hb, hv⟩ := mem_filter.mp hz
    obtain ⟨hi, hjk⟩ := mem_product.mp hb
    obtain ⟨hj, hk⟩ := mem_product.mp hjk
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨hk, mem_product.mpr ⟨hj, hi⟩⟩, ?_⟩
    simpa [smooth3Val, mul_comm, mul_left_comm, mul_assoc] using hv
  · intro z hz w hw h
    have h1 := congrArg (fun e : ℕ × ℕ × ℕ => e.2.2) h
    have h2 := congrArg (fun e : ℕ × ℕ × ℕ => e.2.1) h
    have h3 := congrArg (fun e : ℕ × ℕ × ℕ => e.1) h
    exact Prod.ext h1 (Prod.ext h2 h3)
  · intro z hz
    obtain ⟨hb, hv⟩ := mem_filter.mp hz
    obtain ⟨hk, hji⟩ := mem_product.mp hb
    obtain ⟨hj, hi⟩ := mem_product.mp hji
    refine ⟨(z.2.2, z.2.1, z.1), ?_, rfl⟩
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨hi, mem_product.mpr ⟨hj, hk⟩⟩, ?_⟩
    simpa [smooth3Val, mul_comm, mul_left_comm, mul_assoc] using hv
end ErdosProblems.Erdos269.PaperR9

open Finset
open ErdosProblems in
open ErdosProblems.Erdos269 in
open ErdosProblems.Erdos269.PaperR9 in
theorem solution (a : ℕ) :
    orderedDigitExact a = dyadicOrderedBlockDigit235 a := by
  have hc2 := purePrefixCount_correct (p := 2) (q := 3) (r := 5)
    (by decide) (by decide) (by decide) a
  have hc3 := purePrefixCount_correct (p := 3) (q := 2) (r := 5)
    (by decide) (by decide) (by decide) (Nat.log 3 (2 ^ (a + 1)))
  rw [smoothCountLT_swap_first_second 3 2 5] at hc3
  have hc5 := purePrefixCount_correct (p := 5) (q := 2) (r := 3)
    (by decide) (by decide) (by decide) (Nat.log 5 (2 ^ (a + 1)))
  rw [smoothCountLT_swap_first_third 5 2 3, smoothCountLT_swap_first_second 3 2 5] at hc5
  have hwidth : pairCountChecked 3 5 (2 ^ (a + 1)) = (dyadicSmoothShell235 a).card := by
    have hd := restrictedLogFloorSum_succ_sub 2 3 5 a (by decide) (by decide) (by decide)
    have he : ∀ e, smoothCountLT 2 3 5 (2 ^ e) = restrictedLogFloorSum 2 3 5 e := by
      intro e
      exact restrictedPurePowerCount_eq_restrictedLogFloorSum 2 3 5 e
        (by decide) (by decide) (by decide)
    rw [← he (a + 1), ← he a] at hd
    rw [pairCountChecked_correct (by decide : 1 < 3) (by decide : 1 < 5)]
    rw [dyadicSmoothShell235, strictSmoothShell_card 2 3 5
      (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.le_succ a))]
    exact hd.symm
  unfold orderedDigitExact
  dsimp only
  rw [hc2, hc3, hc5, hwidth]
  simp only [dyadicOrderedBlockDigit235, beforeThreshold_eq_prefix_sub]

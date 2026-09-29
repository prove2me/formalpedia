-- Prove2me | solution 1 for erdos257_irrational_support_series_of_tail
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T02:54:19.169068+00:00
-- url     : https://prove2.me/submissions/2d721028-35a1-415e-b161-f665afa0ffbf

import Theorems.Thm_Erdos249257_summable_erdosSupport_indicator
import Mathlib

noncomputable section
open Erdos249257

theorem solution (b : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (B : ℕ)
    (hTail : Irrational
      (erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n})) :
    Irrational (erdosSupportSeries b A) := by
  classical
  have hIndicator (a : ℕ) :
      Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
        = Set.indicator {n : ℕ | n ∈ A ∧ n ≤ B}
            (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
          + Set.indicator {n : ℕ | n ∈ A ∧ B < n}
            (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a := by
    by_cases hA : a ∈ A
    · by_cases hB : a ≤ B
      · rw [Set.indicator_of_mem hA,
          Set.indicator_of_mem
            (show a ∈ {n : ℕ | n ∈ A ∧ n ≤ B} from ⟨hA, hB⟩),
          Set.indicator_of_notMem
            (show a ∉ {n : ℕ | n ∈ A ∧ B < n} by
              rintro ⟨-, h2⟩; omega)]
        ring
      · rw [Set.indicator_of_mem hA,
          Set.indicator_of_notMem
            (show a ∉ {n : ℕ | n ∈ A ∧ n ≤ B} by
              rintro ⟨-, h2⟩; exact hB h2),
          Set.indicator_of_mem
            (show a ∈ {n : ℕ | n ∈ A ∧ B < n} from ⟨hA, by omega⟩)]
        ring
    · rw [Set.indicator_of_notMem hA,
        Set.indicator_of_notMem
          (show a ∉ {n : ℕ | n ∈ A ∧ n ≤ B} by
            rintro ⟨h1, -⟩; exact hA h1),
        Set.indicator_of_notMem
          (show a ∉ {n : ℕ | n ∈ A ∧ B < n} by
            rintro ⟨h1, -⟩; exact hA h1)]
      ring
  have hPrefixSummable :=
    summable_erdosSupport_indicator b {n : ℕ | n ∈ A ∧ n ≤ B} hb
  have hTailSummable :=
    summable_erdosSupport_indicator b {n : ℕ | n ∈ A ∧ B < n} hb
  have hSplit :
      erdosSupportSeries b A
        = (∑ a ∈ Finset.range (B + 1),
            Set.indicator {n : ℕ | n ∈ A ∧ n ≤ B}
              (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a)
          + erdosSupportSeries b {n : ℕ | n ∈ A ∧ B < n} := by
    have hTsum :
        erdosSupportSeries b A
          = (∑' a : ℕ, Set.indicator {n : ℕ | n ∈ A ∧ n ≤ B}
              (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a)
            + ∑' a : ℕ, Set.indicator {n : ℕ | n ∈ A ∧ B < n}
              (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a := by
      unfold erdosSupportSeries
      rw [← hPrefixSummable.tsum_add hTailSummable]
      exact tsum_congr hIndicator
    rw [hTsum]
    congr 1
    refine tsum_eq_sum fun a ha => ?_
    have haB : ¬ a ≤ B := fun h => ha (Finset.mem_range.mpr (by omega))
    exact Set.indicator_of_notMem
      (by rintro ⟨-, h2⟩; exact haB h2) _
  have hPrefixRational :
      ∃ p : ℚ, (p : ℝ)
        = ∑ a ∈ Finset.range (B + 1),
            Set.indicator {n : ℕ | n ∈ A ∧ n ≤ B}
              (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a := by
    refine ⟨∑ a ∈ Finset.range (B + 1),
      if a ∈ A ∧ a ≤ B then (1 : ℚ) / ((b : ℚ) ^ a - 1) else 0, ?_⟩
    rw [Rat.cast_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : a ∈ A ∧ a ≤ B
    · rw [if_pos h, Set.indicator_of_mem
        (show a ∈ {n : ℕ | n ∈ A ∧ n ≤ B} from h)]
      push_cast
      ring
    · rw [if_neg h, Set.indicator_of_notMem
        (show a ∉ {n : ℕ | n ∈ A ∧ n ≤ B} from h), Rat.cast_zero]
  obtain ⟨p, hp⟩ := hPrefixRational
  rw [hSplit, ← hp]
  exact hTail.ratCast_add p

-- Prove2me | solution 1 for ErdosProblems.Erdos243.LcmRecordCrossing.sum_firstCrossing_partition
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T05:53:18.33712+00:00
-- url     : https://prove2.me/submissions/cce3702b-babe-4222-94cb-3dd4da4107ef

import Theorems.Thm_ErdosProblems_Erdos243_LcmRecordCrossing_exists_unique_firstCrossing
open ErdosProblems.Erdos243.LcmRecordCrossing

theorem solution (s : Finset ℕ) (U t : ℕ → ℕ)
    (N : ℕ) (w : ℕ → ℝ)
    (hzero : ∀ k ∈ s, U 0 < t k)
    (hN : ∀ k ∈ s, ∃ j ≤ N, t k ≤ U j) :
    ∑ k ∈ s, w k =
      ∑ n ∈ Finset.range N, ∑ k ∈ s,
        if FirstCrossing U (t k) n then w k else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  obtain ⟨n, hn, hunique⟩ := exists_unique_firstCrossing U (t k) N
    (hzero k hk) (hN k hk)
  have hiff : ∀ m ∈ Finset.range N, FirstCrossing U (t k) m ↔ m = n := by
    intro m hm
    constructor
    · intro h
      exact hunique m ⟨Finset.mem_range.mp hm, h⟩
    · intro h
      simpa only [h] using hn.2
  symm
  calc
    ∑ m ∈ Finset.range N, (if FirstCrossing U (t k) m then w k else 0) =
        ∑ m ∈ Finset.range N, (if m = n then w k else 0) := by
      apply Finset.sum_congr rfl
      intro m hm
      simp only [hiff m hm]
    _ = w k := by simp [Finset.mem_range.mpr hn.1]



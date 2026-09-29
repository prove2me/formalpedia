-- Prove2me | solution 1 for erdos257_binary_weighted_residue_slice_all_base
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T13:46:09.180432+00:00
-- url     : https://prove2.me/submissions/673ae808-28bb-4350-9f6e-ac69bd974cdd

import Theorems.Thm_erdos257_weighted_support_paper_theorem

noncomputable section

theorem solution
    (H : Set ℕ) (m r : ℕ) (hzero : 0 ∉ H) (hinf : H.Infinite)
    (hweighted : ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted 2 H)
    (hclass : (H ∩ {n : ℕ | n % m = r}).Infinite) :
    ∀ b : ℕ, 2 ≤ b →
      Irrational (Erdos249257.erdosSupportSeries b
        (H ∩ {n : ℕ | n % m = r})) := by
  intro b hb
  exact erdos257_weighted_support_paper_theorem.2
    H hzero hinf hweighted (H ∩ {n : ℕ | n % m = r})
    Set.inter_subset_left hclass b hb

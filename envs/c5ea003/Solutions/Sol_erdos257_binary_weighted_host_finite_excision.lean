-- Prove2me | solution 1 for erdos257_binary_weighted_host_finite_excision
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T02:27:23.596138+00:00
-- url     : https://prove2.me/submissions/0573a6b6-9ddd-44f3-9d43-0b22ff894c6a

import Theorems.Thm_erdos257_weighted_support_paper_theorem

noncomputable section

theorem solution
    (H F : Set ℕ) (hH0 : 0 ∉ H) (hHInf : H.Infinite)
    (hWeighted : ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted 2 H)
    (hF : F.Finite) :
    ∀ b : ℕ, 2 ≤ b →
      Irrational (Erdos249257.erdosSupportSeries b (H \ F)) := by
  intro b hb
  exact erdos257_weighted_support_paper_theorem.2
    H hH0 hHInf hWeighted (H \ F) Set.diff_subset
    (hHInf.diff hF) b hb

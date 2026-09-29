-- Prove2me | solution 1 for erdos257_weighted_support_paper_theorem
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T02:17:44.078361+00:00
-- url     : https://prove2.me/submissions/7d127708-d85c-471e-8a7d-da25387945b3

import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_finitePrimeWeighted_fixedBase_hereditary
import Theorems.Thm_ErdosProblems_Erdos257_PaperCompleteR8_divisibilityWeightedClaim

noncomputable section

theorem solution :
    (∀ (b : ℕ) (H : Set ℕ), 2 ≤ b → 0 ∉ H → H.Infinite →
      ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted b H →
      ∀ A : Set ℕ, A ⊆ H → A.Infinite →
        Irrational (Erdos249257.erdosSupportSeries b A)) ∧
    (∀ H : Set ℕ, 0 ∉ H → H.Infinite →
      ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted 2 H →
      ∀ A : Set ℕ, A ⊆ H → A.Infinite →
        ∀ b : ℕ, 2 ≤ b →
          Irrational (Erdos249257.erdosSupportSeries b A)) := by
  constructor
  · intro b H hb hH0 _ hweighted A hAH hA
    exact ErdosProblems.Erdos257.PaperCompleteR8.finitePrimeWeighted_fixedBase_hereditary
      b H hb hH0 hweighted A hAH hA
  · intro H hH0 _ hweighted A hAH hA b hb
    exact ErdosProblems.Erdos257.PaperCompleteR8.divisibilityWeightedClaim.2
      H hH0 hweighted A hAH hA b hb

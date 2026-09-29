-- Prove2me | solution 1 for erdos257_eventual_weighted_host_irrationality
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-25T02:58:32.400876+00:00
-- url     : https://prove2.me/submissions/e58f3223-d913-48a6-81ed-dda22cb925ad

import Theorems.Thm_erdos257_weighted_support_paper_theorem
import Theorems.Thm_erdos257_irrational_support_series_of_tail
import Mathlib

noncomputable section

theorem solution
    (H A : Set ℕ) (N : ℕ)
    (hH0 : 0 ∉ H)
    (hWeighted : ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted 2 H)
    (hAInf : A.Infinite)
    (hTailH : {n : ℕ | n ∈ A ∧ N < n} ⊆ H)
    (b : ℕ) (hb : 2 ≤ b) :
    Irrational (Erdos249257.erdosSupportSeries b A) := by
  have hTailInf : Set.Infinite {n : ℕ | n ∈ A ∧ N < n} := by
    have hDiff : (A \ {n : ℕ | n ≤ N}).Infinite :=
      hAInf.diff (Set.finite_le_nat N)
    have hEq : A \ {n : ℕ | n ≤ N} =
        {n : ℕ | n ∈ A ∧ N < n} := by
      ext n
      simp [Set.mem_diff, Nat.not_le]
    simpa only [hEq] using hDiff
  have hHInf : H.Infinite := by
    intro hHFinite
    exact hTailInf (hHFinite.subset hTailH)
  have hTailIrr : Irrational
      (Erdos249257.erdosSupportSeries b
        {n : ℕ | n ∈ A ∧ N < n}) :=
    erdos257_weighted_support_paper_theorem.2
      H hH0 hHInf hWeighted
      {n : ℕ | n ∈ A ∧ N < n} hTailH hTailInf b hb
  exact erdos257_irrational_support_series_of_tail b A hb N hTailIrr

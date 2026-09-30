-- Prove2me | solution 1 for lean_workbook_plus_73036
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:10:14.853089+00:00
-- url     : https://prove2.me/submissions/6a5a7252-1f8a-477a-ad13-32958b37e0fc

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

theorem solution (s : ℕ → ℝ) (hs : ∀ n, s (n + 1) = (s n + s (n - 1)) / 2) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |s n - s (n - 1)| < ε := by
  have hclosed (n : ℕ) : s n = s 0 := by
    induction n using Nat.twoStepInduction with
    | zero => rfl
    | one =>
        have h := hs 0
        norm_num only [Nat.zero_add, Nat.sub_self] at h
        linarith
    | more n ih0 ih1 =>
        calc
          s (n + 2) = (s (n + 1) + s n) / 2 := by simpa using hs (n + 1)
          _ = s 0 := by rw [ih0, ih1]; ring
  intro ε hε
  refine ⟨0, fun n _hn => ?_⟩
  rw [hclosed n, hclosed (n - 1), sub_self, abs_zero]
  exact hε

#print axioms solution

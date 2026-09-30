-- Prove2me | solution 1 for lean_workbook_plus_79471
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T01:45:21.714029+00:00
-- url     : https://prove2.me/submissions/3b3e4878-78b1-4e80-a05d-b08b1bdae6ec

import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

theorem solution (n k : ℕ) (h₀ : 0 < k ∧ 0 < n) (h₁ : n ≥ k) :
    Nat.choose n (k - 1) = Nat.choose n (n - k + 1) := by
  have hk : k - 1 ≤ n := by omega
  have hsub : n - (k - 1) = n - k + 1 := by omega
  simpa [hsub] using (Nat.choose_symm hk).symm

#print axioms solution

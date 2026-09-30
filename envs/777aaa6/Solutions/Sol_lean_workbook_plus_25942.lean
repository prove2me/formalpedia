-- Prove2me | solution 1 for lean_workbook_plus_25942
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T05:44:11.568732+00:00
-- url     : https://prove2.me/submissions/6cd69f88-db19-4a56-b1c7-19823cb78876

import Mathlib.Combinatorics.Additive.ErdosGinzburgZiv
import Mathlib.Tactic

private theorem exact_size_zero_sum (n : ℕ) (A : Finset ℕ)
    (hA : 2 * n - 1 ≤ A.card) :
    ∃ B : Finset ℕ, B ⊆ A ∧ B.card = n ∧ n ∣ B.sum (fun x => x) := by
  obtain ⟨B, hBA, hB, hsum⟩ :=
    Int.erdos_ginzburg_ziv (n := n) (s := A) (fun x => (x : ℤ)) hA
  refine ⟨B, hBA, hB, ?_⟩
  have hcast : (n : ℤ) ∣ ((B.sum (fun x => x) : ℕ) : ℤ) := by
    simpa only [Nat.cast_sum] using hsum
  exact_mod_cast hcast

theorem solution (n : ℕ) (A : Finset ℕ) (hA : A.card = 2 * n - 1) :
    ∃ B : Finset ℕ, B ⊆ A ∧ n ∣ B.sum (fun x => x) := by
  obtain ⟨B, hBA, _, hsum⟩ := exact_size_zero_sum n A hA.ge
  exact ⟨B, hBA, hsum⟩

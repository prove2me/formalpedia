-- Prove2me | Theorems.Thm_gpy_exists_two_primes_of_mainTerm_crossing
-- name    : gpy_exists_two_primes_of_mainTerm_crossing
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T08:54:47.446538+00:00
-- url     : https://prove2.me/theorems/50b6769e-8ce3-4a7a-910b-701672cc61f6
-- title:
--   Abstract threshold step: main-term crossing forces two primes in one translate
-- statement:
--   If the first moment is within E1 of A and the second moment within E2 of B, and A + E1 < B - E2, then the second moment exceeds the first and the criterion applies. All local definitions are written out in Mathlib terms.
-- source:
--   GPY ratio analysis: threshold, main-term approximations, and BV level cap

import Mathlib
open Classical

theorem gpy_exists_two_primes_of_mainTerm_crossing {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (lam : (Fin k → ℕ) → ℝ) {x y : ℕ} (A B E1 E2 : ℝ) (hS1 : abs ((∑ n ∈ Finset.Ioc x y, ((∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2)) - A) ≤ E1) (hS2 : abs ((∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) * ((∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2)) - B) ≤ E2) (hcross : A + E1 < B - E2) : ∃ n ∈ Finset.Ioc x y, ∃ i j, i ≠ j ∧ Nat.Prime (n + h i) ∧ Nat.Prime (n + h j) := by sorry

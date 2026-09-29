-- Prove2me | solution 1 for lean_workbook_plus_54504
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:41:15.70335+00:00
-- url     : https://prove2.me/submissions/5437881e-d962-4467-8bda-bd9a694d8d16

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :
  ∀ k : ℕ, (k ≡ 0 [ZMOD 10] ∧ k ≡ 0 [ZMOD 4] ∨ k ≡ 1 [ZMOD 10] ∨ k ≡ 2 [ZMOD 10] ∧ k ≡ 0 [ZMOD 4] ∨ k ≡ 2 [ZMOD 10] ∧ k ≡ 2 [ZMOD 4] ∨ k ≡ 3 [ZMOD 10] ∧ k ≡ 1 [ZMOD 4] ∨ k ≡ 3 [ZMOD 10] ∧ k ≡ 3 [ZMOD 4] ∨ k ≡ 4 [ZMOD 10] ∧ k ≡ 0 [ZMOD 4] ∨ k ≡ 4 [ZMOD 10] ∧ k ≡ 2 [ZMOD 4] ∨ k ≡ 5 [ZMOD 10] ∨ k ≡ 6 [ZMOD 10] ∨ k ≡ 7 [ZMOD 10] ∧ k ≡ 1 [ZMOD 4] ∨ k ≡ 7 [ZMOD 10] ∧ k ≡ 3 [ZMOD 4] ∨ k ≡ 8 [ZMOD 10] ∧ k ≡ 0 [ZMOD 4] ∨ k ≡ 8 [ZMOD 10] ∧ k ≡ 2 [ZMOD 4] ∨ k ≡ 9 [ZMOD 10] ∧ k ≡ 1 [ZMOD 4] ∨ k ≡ 9 [ZMOD 10] ∧ k ≡ 3 [ZMOD 4]) → (k^k ≡ 0 [ZMOD 10] ∨ k^k ≡ 1 [ZMOD 10] ∨ k^k ≡ 2 [ZMOD 10] ∨ k^k ≡ 3 [ZMOD 10] ∨ k^k ≡ 4 [ZMOD 10] ∨ k^k ≡ 5 [ZMOD 10] ∨ k^k ≡ 6 [ZMOD 10] ∨ k^k ≡ 7 [ZMOD 10] ∨ k^k ≡ 8 [ZMOD 10] ∨ k^k ≡ 9 [ZMOD 10]) := by
  (intros; simp only [Int.ModEq, Nat.ModEq] at *; omega)

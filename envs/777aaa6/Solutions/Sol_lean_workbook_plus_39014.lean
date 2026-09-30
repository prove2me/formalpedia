-- Prove2me | solution 1 for lean_workbook_plus_39014
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T23:07:29.495126+00:00
-- url     : https://prove2.me/submissions/29d24df0-ff94-4c9a-b8ab-d6f11478a7c1

import Mathlib.Analysis.Complex.Basic

theorem solution (f : ℕ → ℕ) (hf: f 1 = 5 ∧ ∀ n, f (f n) = 4*n + 9 ∧ f (2^n) = 2^(n+1) + 3) : ∃ f : ℕ → ℕ, f 1 = 5 ∧ ∀ n, f (f n) = 4*n + 9 ∧ f (2^n) = 2^(n+1) + 3 :=
  ⟨f, hf⟩

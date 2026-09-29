-- Prove2me | solution 1 for lean_workbook_plus_17478
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:28:50.993711+00:00
-- url     : https://prove2.me/submissions/fd1e988c-1468-4923-a73e-d64198afcec3

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (n : ℕ) (f : ℕ → ℕ) (hf: f 1 = 1 ∧ f 2 = 4 ∧ f 3 = 22 ∧ f 4 = 316 ∧ f 5 = 6976 ∧ f 6 = 373024 ∧ f 7 = 32252032 ∧ f 8 = 6619979776 ∧ f 9 = 2253838544896 ∧ f 10 = 1810098020122624): (n >= 5 ∧ n <= 10) → f n % 8 = 0 := by
  intro hn
  rcases hn with ⟨hl, hu⟩
  interval_cases n <;> simp_all

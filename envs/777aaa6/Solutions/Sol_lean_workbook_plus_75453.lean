-- Prove2me | solution 1 for lean_workbook_plus_75453
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:27:49.578713+00:00
-- url     : https://prove2.me/submissions/8bfa87ce-7d05-4519-b135-f42ca3ed9f7f

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution : ∀ n : ℕ, (n % 2 = 0 ↔ Even n) ∧ (n % 2 = 1 ↔ Odd n) := by
  intro n
  exact ⟨Nat.even_iff.symm, Nat.odd_iff.symm⟩

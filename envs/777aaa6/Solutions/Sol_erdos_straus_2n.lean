-- Prove2me | solution 1 for erdos_straus_2n
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-23T17:37:23.757497+00:00
-- url     : https://prove2.me/submissions/f4be6105-882c-4eea-9fc5-39d46f06c0d4

import Mathlib

theorem solution :
    ∀ n : ℕ, 2 ≤ n →
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧
      2 * a * b = n * (b + a) := by
  intro n hn
  use n, n
  refine ⟨?_, ?_, ?_⟩
  · linarith
  · linarith
  · ring

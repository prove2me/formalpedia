-- Prove2me | solution 1 for lean_workbook_plus_65467
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:55:15.349826+00:00
-- url     : https://prove2.me/submissions/e757c315-518a-4ad9-8282-b190f4c5498c

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution {f : ℕ → ℕ} (hf : ∀ p, Nat.Prime p → f (p - 1) = p - 1) (hf_le : ∀ n, f n ≤ n) : f 1 = 1 := by
  simpa using hf 2 Nat.prime_two

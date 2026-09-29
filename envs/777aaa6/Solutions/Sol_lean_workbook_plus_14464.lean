-- Prove2me | solution 1 for lean_workbook_plus_14464
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:29:11.497481+00:00
-- url     : https://prove2.me/submissions/df790571-062c-425a-a56c-fcfefa791cb2

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (n : ℕ) (u : ℕ → ℕ) (h₁ : u 1 = 3) (h₂ : ∀ n, u (n+1) = u n + 2) : u n = 2 * n + 1 := by
  have h0 : u 0 = 1 := by
    have hzero := h₂ 0
    norm_num [h₁] at hzero
    omega
  induction n with
  | zero => simpa using h0
  | succ n ih => rw [h₂,ih]; omega

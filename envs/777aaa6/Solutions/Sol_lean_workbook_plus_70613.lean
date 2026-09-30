-- Prove2me | solution 1 for lean_workbook_plus_70613
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T07:54:25.851389+00:00
-- url     : https://prove2.me/submissions/e1a0acdc-037c-436e-9dbf-97c5b41e24e4

import Mathlib
set_option autoImplicit false

theorem solution (n : ℕ) (f : ℕ → ℕ)
    (h0 : ∀ x y, x < y → f x < f y) (_h1 : f 1 ≥ 1) : f n ≥ n := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have h := h0 n (n + 1) (by omega)
    omega

#print axioms solution

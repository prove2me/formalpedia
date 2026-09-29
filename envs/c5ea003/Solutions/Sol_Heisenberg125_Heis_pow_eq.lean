-- Prove2me | solution 1 for Heisenberg125.Heis.pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T03:46:24.428172+00:00
-- url     : https://prove2.me/submissions/8e791d47-cc08-4099-a4b7-c61add0fc702

import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
open Heisenberg125 Heisenberg125.Heis in
theorem solution {p : ℕ} (g : Heis p) (n : ℕ) :
    g ^ n = ⟨(n : ZMod p) * g.a, (n : ZMod p) * g.b,
      (n : ZMod p) * g.c + (n.choose 2 : ℕ) * (g.a * g.b)⟩ := by
  induction n with
  | zero =>
    ext <;> simp
  | succ n ih =>
    -- `g^(n+1) = g^n · g`, and `C(n+1, 2) = C(n, 2) + n`
    rw [pow_succ, ih]
    ext
    · simp only [mul_a]
      push_cast
      ring
    · simp only [mul_b]
      push_cast
      ring
    · simp only [mul_c]
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
      push_cast
      ring

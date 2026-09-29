-- Prove2me | Theorems.Thm_mertens_constant_transcendental
-- name    : mertens_constant_transcendental
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-06-01T03:29:12.446618+00:00
-- url     : https://prove2.me/theorems/f1c2eb63-0db3-48dc-96a5-a5de03b2a212
-- statement:
--   Meissel-Mertens constant M ≈ 0.2615: The constant in ∑_{p≤x} 1/p = log log x + M. Conjectured irrational/transcendental but neither proved.
-- source:
--   https://en.wikipedia.org/wiki/Meissel%E2%80%93Mertens_constant

import Mathlib

import Mathlib

theorem mertens_constant_transcendental :
    Irrational (Real.eulerMascheroniConstant +
      ∑' p : {p : ℕ // Nat.Prime p},
        (Real.log (1 - 1 / (p : ℝ)) + 1 / (p : ℝ))) := by
  sorry

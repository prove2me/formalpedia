-- Prove2me | Theorems.Thm_fermat_little_p
-- name    : fermat_little_p
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:30:51.389007+00:00
-- url     : https://prove2.me/theorems/84aaf8d3-48e3-4b17-9627-07a33c41b6d3
-- statement:
--   **Fermat's Little Theorem (general).** For any prime p and any integer a, p divides a^p − a. This generalizes all the specific cases: p=2,3,5,7,11,13,... The proof uses the ZMod characterization: (a^p − a : ZMod p) = 0, which follows from ZMod.pow_card (the Frobenius endomorphism). This is the foundation of many results in algebraic number theory and the starting point for primality tests.

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem fermat_little_p (p : ℕ) (hp : p.Prime) (a : ℤ) : (p : ℤ) ∣ a ^ p - a := by sorry

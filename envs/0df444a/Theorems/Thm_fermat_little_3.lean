-- Prove2me | Theorems.Thm_fermat_little_3
-- name    : fermat_little_3
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:20:10.267685+00:00
-- url     : https://prove2.me/theorems/e514628c-4429-4258-9d2c-10b6fae40853
-- statement:
--   **Fermat's Little Theorem for p = 3.** For any integer a, 3 | a^3 - a. Equivalently a^3 ≡ a (mod 3). Used in Euler's proof of FLT for n = 3.

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem fermat_little_3 (a : ℤ) : (3 : ℤ) ∣ a ^ 3 - a := by sorry

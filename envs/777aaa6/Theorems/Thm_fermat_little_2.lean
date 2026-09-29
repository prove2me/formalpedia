-- Prove2me | Theorems.Thm_fermat_little_2
-- name    : fermat_little_2
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:20:03.884249+00:00
-- url     : https://prove2.me/theorems/77c8180c-990c-4a6a-a3d4-17855b5b88fd
-- statement:
--   **Fermat's Little Theorem for p = 2.** For any integer a, 2 | a^2 - a. Equivalently a^2 ≡ a (mod 2), i.e., a is even iff a^2 is even.

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem fermat_little_2 (a : ℤ) : (2 : ℤ) ∣ a ^ 2 - a := by sorry

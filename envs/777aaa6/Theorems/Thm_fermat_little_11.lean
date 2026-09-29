-- Prove2me | Theorems.Thm_fermat_little_11
-- name    : fermat_little_11
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:20:21.51235+00:00
-- url     : https://prove2.me/theorems/d697b1a8-7761-4045-92a8-112b560c4076
-- statement:
--   **Fermat's Little Theorem for p = 11.** For any integer a, 11 | a^11 - a. Equivalently a^11 ≡ a (mod 11).

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem fermat_little_11 (a : ℤ) : (11 : ℤ) ∣ a ^ 11 - a := by sorry

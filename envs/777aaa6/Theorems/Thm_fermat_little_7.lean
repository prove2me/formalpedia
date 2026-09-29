-- Prove2me | Theorems.Thm_fermat_little_7
-- name    : fermat_little_7
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:20:16.185017+00:00
-- url     : https://prove2.me/theorems/0f654aa7-3f0d-4ee6-82c6-741347cb7033
-- statement:
--   **Fermat's Little Theorem for p = 7.** For any integer a, 7 | a^7 - a. Equivalently a^7 ≡ a (mod 7). Connected to Lamé's 1839 proof of FLT for n = 7.

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem fermat_little_7 (a : ℤ) : (7 : ℤ) ∣ a ^ 7 - a := by sorry

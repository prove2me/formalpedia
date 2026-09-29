-- Prove2me | Theorems.Thm_euler_phi7
-- name    : euler_phi7
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:25:55.365732+00:00
-- url     : https://prove2.me/theorems/1c9c4a14-17a7-491d-9769-3d6225e922ad
-- statement:
--   **Euler's Theorem for p=7, φ(7)=6.** If 7 ∤ a then 7 | a^6 − 1. Equivalently, a^6 ≡ 1 (mod 7). Used in Lamé's FLT-7 argument and related to the structure of the multiplicative group mod 7.

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem euler_phi7 (a : ℤ) (h : ¬(7 : ℤ) ∣ a) : (7 : ℤ) ∣ a ^ 6 - 1 := by sorry

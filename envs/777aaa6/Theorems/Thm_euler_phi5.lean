-- Prove2me | Theorems.Thm_euler_phi5
-- name    : euler_phi5
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:25:50.741147+00:00
-- url     : https://prove2.me/theorems/aa7166ea-5916-43a6-8fe6-9fb72bf63a8d
-- statement:
--   **Euler's Theorem for p=5, φ(5)=4.** If 5 ∤ a then 5 | a^4 − 1. Equivalently, a^4 ≡ 1 (mod 5) for all a coprime to 5. Used in the analysis of a^5 ≡ a (mod 5) and in Dirichlet's FLT-5 argument.

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem euler_phi5 (a : ℤ) (h : ¬(5 : ℤ) ∣ a) : (5 : ℤ) ∣ a ^ 4 - 1 := by sorry

-- Prove2me | Theorems.Thm_euler_phi3
-- name    : euler_phi3
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:25:46.128299+00:00
-- url     : https://prove2.me/theorems/358bb89e-5464-4716-96c2-679d0a705b35
-- statement:
--   **Euler's Theorem for p=3, φ(3)=2.** If 3 ∤ a then 3 | a^2 − 1. Equivalently, a^2 ≡ 1 (mod 3) for all a coprime to 3. This is the special case of Fermat-Euler: a^φ(p) ≡ 1 (mod p) for prime p and gcd(a,p)=1.

import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic

theorem euler_phi3 (a : ℤ) (h : ¬(3 : ℤ) ∣ a) : (3 : ℤ) ∣ a ^ 2 - 1 := by sorry

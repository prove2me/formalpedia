-- Prove2me | Theorems.Thm_gcd_coprime_mul
-- name    : gcd_coprime_mul
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:14:03.178893+00:00
-- url     : https://prove2.me/theorems/2ffd4dec-d875-4db3-82aa-4a71359e9116
-- statement:
--   **Coprimality is preserved under products.** If gcd(a,b) = 1 and gcd(a,c) = 1, then gcd(a, b*c) = 1. This is a fundamental property of coprimality: a is coprime to any product of numbers each coprime to it. Used in descent arguments where coprimality must be tracked through multiplicative factorizations.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem gcd_coprime_mul (a b c : ℤ) (h1 : Int.gcd a b = 1) (h2 : Int.gcd a c = 1) : Int.gcd a (b * c) = 1 := by sorry

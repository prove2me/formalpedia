-- Prove2me | Theorems.Thm_gcd_coprime_sub
-- name    : gcd_coprime_sub
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:14:07.886507+00:00
-- url     : https://prove2.me/theorems/1260fffb-9ee4-4535-94d0-846319945fef
-- statement:
--   **GCD of coprime difference.** If gcd(a, b) = 1 then gcd(a - b, b) = 1. Subtraction by b, like addition, preserves coprimality with b. This is the 'other direction' of gcd_coprime_add and follows from the same Euclidean algorithm property.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem gcd_coprime_sub (a b : ℤ) (h : Int.gcd a b = 1) : Int.gcd (a - b) b = 1 := by sorry

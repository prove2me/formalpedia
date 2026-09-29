-- Prove2me | Theorems.Thm_gcd_sum_eq
-- name    : gcd_sum_eq
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T06:14:11.977718+00:00
-- url     : https://prove2.me/theorems/d5ad499f-db29-49e0-bbdb-a2261c00cdc0
-- statement:
--   **GCD of sum equals GCD of summand.** gcd(a+b, a) = gcd(b, a). This is the fundamental Euclidean algorithm step: replacing one argument by its remainder. It implies that gcd(a+b, a) = gcd(a, b) by commutativity of gcd.

import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.GCD

theorem gcd_sum_eq (a b : ℤ) : Int.gcd (a + b) a = Int.gcd b a := by sorry

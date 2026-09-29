-- Prove2me | Theorems.Thm_fltp_lte
-- name    : fltp_lte
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T10:50:57.923958+00:00
-- url     : https://prove2.me/theorems/cfca6da8-a669-4d9a-849b-c50e907a0ed5
-- statement:
--   Lifting the Exponent Lemma (LTE) for FLT-p: If p is an odd prime, p divides a+b, and p does not divide a, then emultiplicity p (a^p + b^p) = emultiplicity p (a+b) + 1. This is the key p-adic valuation identity used in Kummer's approach to Fermat's Last Theorem for regular primes.
-- source:
--   https://en.wikipedia.org/wiki/Lifting-the-exponent_lemma

import Mathlib.NumberTheory.Multiplicity

theorem fltp_lte (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℤ)
    (h_odd : Odd p) (h_dvd : (p : ℤ) ∣ a + b) (h_ndvd : ¬(p : ℤ) ∣ a) :
    emultiplicity (p : ℤ) (a ^ p + b ^ p) =
    emultiplicity (p : ℤ) (a + b) + 1 := by sorry

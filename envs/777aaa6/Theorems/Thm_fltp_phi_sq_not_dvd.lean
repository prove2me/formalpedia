-- Prove2me | Theorems.Thm_fltp_phi_sq_not_dvd
-- name    : fltp_phi_sq_not_dvd
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T10:50:47.647696+00:00
-- url     : https://prove2.me/theorems/7c8dcddc-6554-4b0c-b338-6bf8e5174059
-- statement:
--   If p is an odd prime, p divides a+b, and p does not divide a, then p^2 does not divide Phi_p(a,b) = sum_{i<p} a^i * (-b)^(p-1-i). This is the exact divisibility part of the Lifting-the-Exponent Lemma for the cyclotomic polynomial.
-- source:
--   https://en.wikipedia.org/wiki/Lifting-the-exponent_lemma

import Mathlib.NumberTheory.Multiplicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open Finset in
theorem fltp_phi_sq_not_dvd (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℤ)
    (h_odd : Odd p) (h_dvd : (p : ℤ) ∣ a + b) (h_ndvd : ¬(p : ℤ) ∣ a) :
    ¬(p : ℤ) ^ 2 ∣ ∑ i ∈ range p, a ^ i * (-b) ^ (p - 1 - i) := by sorry

-- Prove2me | Theorems.Thm_fltp_phi_not_sq_dvd
-- name    : fltp_phi_not_sq_dvd
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T11:07:20.988192+00:00
-- url     : https://prove2.me/theorems/f7a41a05-c4ad-4e61-9b39-2c55626c9c66
-- statement:
--   If p is an odd prime, p divides a+b, and p does not divide a, then p^2 does not divide Phi_p(a,b) = sum_{i<p} a^i * (-b)^(p-1-i). This is the exact divisibility half of the Lifting-the-Exponent Lemma for the cyclotomic polynomial Phi_p.
-- source:
--   https://en.wikipedia.org/wiki/Lifting-the-exponent_lemma

import Mathlib.NumberTheory.Multiplicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem fltp_phi_not_sq_dvd (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℤ)
    (h_odd : Odd p) (h_dvd : (p : ℤ) ∣ a + b) (h_ndvd : ¬(p : ℤ) ∣ a) :
    ¬(p : ℤ) ^ 2 ∣ ∑ i ∈ Finset.range p, a ^ i * (-b) ^ (p - 1 - i) := by sorry

-- Prove2me | Theorems.Thm_fltp_emult_phi_eq_one
-- name    : fltp_emult_phi_eq_one
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T11:10:04.129288+00:00
-- url     : https://prove2.me/theorems/d6264aaa-3714-415d-9191-7b9f69fbba91
-- statement:
--   If p is an odd prime, p divides a+b, and p does not divide a, then the p-adic multiplicity (emultiplicity) of Phi_p(a,b) = sum_{i<p} a^i*(-b)^(p-1-i) equals exactly 1. This is the key Lifting-the-Exponent result for the cyclotomic sum.
-- source:
--   https://en.wikipedia.org/wiki/Lifting-the-exponent_lemma

import Mathlib.NumberTheory.Multiplicity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem fltp_emult_phi_eq_one (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℤ)
    (h_odd : Odd p) (h_dvd : (p : ℤ) ∣ a + b) (h_ndvd : ¬(p : ℤ) ∣ a) :
    emultiplicity (p : ℤ) (∑ i ∈ Finset.range p, a ^ i * (-b) ^ (p - 1 - i)) = 1 := by sorry

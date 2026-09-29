-- Prove2me | Theorems.Thm_fltp_phi_dvd_p
-- name    : fltp_phi_dvd_p
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T10:28:46.12857+00:00
-- url     : https://prove2.me/theorems/161b88e4-a4a7-4a19-aa23-fb4c6228db05
-- statement:
--   For any prime p and integers a, b with p | a+b, p divides the cyclotomic factor Phi_p(a,b) = ∑_{i=0}^{p-1} a^i * (-b)^(p-1-i). Proof: In ZMod p, a ≡ -b so each term a^i * (-b)^(p-1-i) ≡ (-b)^i * (-b)^(p-1-i) = (-b)^(p-1), and the sum of p identical terms is p * (-b)^(p-1) = 0 in ZMod p.

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem fltp_phi_dvd_p (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℤ) (h_dvd : (p : ℤ) ∣ a + b) : (p : ℤ) ∣ ∑ i ∈ Finset.range p, a ^ i * (-b) ^ (p - 1 - i) := by sorry

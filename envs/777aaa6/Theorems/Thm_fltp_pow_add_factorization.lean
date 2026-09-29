-- Prove2me | Theorems.Thm_fltp_pow_add_factorization
-- name    : fltp_pow_add_factorization
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T10:37:04.608152+00:00
-- url     : https://prove2.me/theorems/fed3e10d-43dd-4e4a-9e9a-458e5f3de695
-- statement:
--   For any odd natural number p and integers a, b, a^p + b^p = (a+b) * Phi_p(a,b) where Phi_p(a,b) = ∑_{i=0}^{p-1} a^i * (-b)^(p-1-i). This is the algebraic factorization of the sum of odd powers, crucial for Kummer's descent in FLT-p.

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem fltp_pow_add_factorization (p : ℕ) (h_odd : Odd p) (a b : ℤ) : a ^ p + b ^ p = (a + b) * ∑ i ∈ Finset.range p, a ^ i * (-b) ^ (p - 1 - i) := by sorry

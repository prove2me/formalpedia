-- Prove2me | Theorems.Thm_fltp_p_sq_dvd_pow_add
-- name    : fltp_p_sq_dvd_pow_add
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T10:39:10.69047+00:00
-- url     : https://prove2.me/theorems/f1c6f407-cce3-4b69-b179-6de3fc8b6e01
-- statement:
--   For an odd prime p and integers a, b with p | a+b, we have p² | a^p + b^p. Proof: a^p + b^p = (a+b)*Phi_p(a,b) by factorization; p | (a+b) by hypothesis; p | Phi_p(a,b) since each term becomes (-b)^(p-1) in ZMod p and there are p terms; hence p² | (a+b)*Phi_p(a,b) = a^p+b^p.

import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem fltp_p_sq_dvd_pow_add (p : ℕ) [hp : Fact (Nat.Prime p)] (a b : ℤ) (h_odd : Odd p) (h_dvd : (p : ℤ) ∣ a + b) : (p : ℤ) ^ 2 ∣ a ^ p + b ^ p := by sorry

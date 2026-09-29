-- Prove2me | Theorems.Thm_cyclotomic_phi5_congruence
-- name    : cyclotomic_phi5_congruence
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T05:40:41.524487+00:00
-- url     : https://prove2.me/theorems/20f33c6b-bfa3-41c6-9f57-a39793b1d28a
-- statement:
--   **Key congruence for the gcd step in Dirichlet's FLT-5 proof.** The fifth cyclotomic polynomial Φ₅(a,b) = a^4 − a^3b + a^2b^2 − ab^3 + b^4 satisfies Φ₅(a,b) − 5b^4 = (a+b)·(a^3 − 2a^2b + 3ab^2 − 4b^3). Combined with the fact that (a+b) | a^5+b^5, this yields: if d = gcd(a+b, Φ₅(a,b)) then d | 5b^4. When gcd(a,b) = 1, one shows gcd(a+b, b) = 1, hence d | 5. This is the heart of the Dirichlet-Legendre proof.

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem cyclotomic_phi5_congruence (a b : ℤ) : a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4 - 5 * b ^ 4 = (a + b) * (a ^ 3 - 2 * a ^ 2 * b + 3 * a * b ^ 2 - 4 * b ^ 3) := by sorry

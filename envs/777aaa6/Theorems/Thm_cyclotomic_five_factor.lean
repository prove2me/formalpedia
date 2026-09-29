-- Prove2me | Theorems.Thm_cyclotomic_five_factor
-- name    : cyclotomic_five_factor
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-12T05:37:26.655681+00:00
-- url     : https://prove2.me/theorems/c279fa2e-8eb5-417e-baf4-49a0fb012832
-- statement:
--   **Cyclotomic factoring for n = 5.** The sum of two fifth powers factors as a^5 + b^5 = (a + b) * Φ₅(a, b), where Φ₅(a,b) = a^4 − a^3b + a^2b^2 − ab^3 + b^4 is the fifth cyclotomic polynomial evaluated at a/b (times b^4). This is the key factoring identity used in the Dirichlet-Legendre proof of Fermat's Last Theorem for n = 5. Over ℤ, this identity holds universally and is provable by ring.

import Mathlib.Data.Int.Basic
import Mathlib.Tactic.Ring

theorem cyclotomic_five_factor (a b : ℤ) : a ^ 5 + b ^ 5 = (a + b) * (a ^ 4 - a ^ 3 * b + a ^ 2 * b ^ 2 - a * b ^ 3 + b ^ 4) := by sorry

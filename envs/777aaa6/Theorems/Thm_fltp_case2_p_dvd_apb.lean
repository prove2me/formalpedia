-- Prove2me | Theorems.Thm_fltp_case2_p_dvd_apb
-- name    : fltp_case2_p_dvd_apb
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T11:16:53.521679+00:00
-- url     : https://prove2.me/theorems/f802106a-53c6-44f6-93fb-2c9d9d9984f9
-- statement:
--   In FLT Case 2: if a^p + b^p = c^p and p divides c (for odd prime p), then p divides a+b. Proof via Fermat's little theorem (x^p = x in ZMod p): a+b = a^p+b^p = c^p = c = 0 mod p.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

theorem fltp_case2_p_dvd_apb (p : ℕ) [hp : Fact (Nat.Prime p)] (a b c : ℕ)
    (heq : a ^ p + b ^ p = c ^ p) (h_dvd_c : p ∣ c) :
    p ∣ a + b := by sorry

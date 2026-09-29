-- Prove2me | Theorems.Thm_fltp_case2_p_dvd_apb
-- name    : fltp_case2_p_dvd_apb
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T11:16:53.521679+00:00
-- url     : https://prove2.me/theorems/c73d93cf-54e7-4c5f-ac4b-72f28a1cfce4
-- statement:
--   In FLT Case 2: if a^p + b^p = c^p and p divides c (for odd prime p), then p divides a+b. Proof via Fermat's little theorem (x^p = x in ZMod p): a+b = a^p+b^p = c^p = c = 0 mod p.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.ZMod.Basic

theorem fltp_case2_p_dvd_apb (p : ℕ) [hp : Fact (Nat.Prime p)] (a b c : ℕ)
    (heq : a ^ p + b ^ p = c ^ p) (h_dvd_c : p ∣ c) :
    p ∣ a + b := by sorry

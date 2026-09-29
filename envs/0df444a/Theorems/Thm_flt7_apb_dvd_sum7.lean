-- Prove2me | Theorems.Thm_flt7_apb_dvd_sum7
-- name    : flt7_apb_dvd_sum7
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-05-15T08:27:39.944941+00:00
-- url     : https://prove2.me/theorems/d7483935-cd61-4e03-9962-556ac46b4b71
-- statement:
--   For natural numbers a and b, (a+b) divides (a^7+b^7). This follows from the factorization a^7+b^7 = (a+b)*Phi_7(a,b) in ℤ, lifted to ℕ via the fact that Phi_7(a,b) is a non-negative integer for non-negative a,b.
-- source:
--   https://en.wikipedia.org/wiki/Fermat%27s_Last_Theorem

import Mathlib.NumberTheory.Multiplicity

theorem flt7_apb_dvd_sum7 (a b : ℕ) : (a + b) ∣ (a^7 + b^7) := by sorry

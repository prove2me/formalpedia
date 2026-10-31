-- Prove2me | Theorems.Thm_gpy_mem_primeFactors_lcm
-- name    : gpy_mem_primeFactors_lcm
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T02:36:03.584768+00:00
-- url     : https://prove2.me/theorems/3801a9d7-dda6-427e-9fad-40ce4c3e7279
-- title:
--   Prime factors of a lcm are the primes dividing a factor
-- statement:
--   For nonzero D and E, p is a prime factor of lcm D E exactly when p is prime and p divides D or p divides E. Formalization Note: the statement uses only Mathlib terms.
-- source:
--   GPY good-count product formula via the fiber bijection, formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_mem_primeFactors_lcm {D E p : ℕ} (hD : D ≠ 0) (hE : E ≠ 0) :
    p ∈ (Nat.lcm D E).primeFactors ↔ Nat.Prime p ∧ (p ∣ D ∨ p ∣ E)  := by sorry

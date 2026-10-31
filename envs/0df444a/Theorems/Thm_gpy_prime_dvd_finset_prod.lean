-- Prove2me | Theorems.Thm_gpy_prime_dvd_finset_prod
-- name    : gpy_prime_dvd_finset_prod
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T02:23:30.293512+00:00
-- url     : https://prove2.me/theorems/5d1c3213-6cfb-48fa-8e85-c478476a3587
-- title:
--   A prime dividing a finset product divides some factor
-- statement:
--   If a prime p divides a finset product, then p divides some factor. Formalization Note: the statement uses only Mathlib terms.
-- source:
--   GPY good-count product formula via the fiber bijection, formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_prime_dvd_finset_prod {ι : Type*} {s : Finset ι} {f : ι → ℕ} {p : ℕ}
    (hp : Nat.Prime p) (h : p ∣ ∏ i ∈ s, f i) : ∃ j ∈ s, p ∣ f j  := by sorry

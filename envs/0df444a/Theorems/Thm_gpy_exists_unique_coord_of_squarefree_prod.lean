-- Prove2me | Theorems.Thm_gpy_exists_unique_coord_of_squarefree_prod
-- name    : gpy_exists_unique_coord_of_squarefree_prod
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T02:25:37.418993+00:00
-- url     : https://prove2.me/theorems/6d6cd4e1-9fcf-4945-90ee-c4c56ce68691
-- title:
--   A prime divisor of a squarefree product sits in exactly one coordinate
-- statement:
--   On a tuple of positive integers with squarefree product, a prime dividing the product divides exactly one coordinate. Formalization Note: the statement uses only Mathlib terms.
-- source:
--   GPY good-count product formula via the fiber bijection, formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_exists_unique_coord_of_squarefree_prod {k : ℕ} {d : Fin k → ℕ}
    {p : ℕ} (hd1 : ∀ j, 1 ≤ d j) (hsq : Squarefree (∏ j, d j)) (hp : Nat.Prime p)
    (hpd : p ∣ ∏ j, d j) : ∃! j, p ∣ d j  := by sorry

-- Prove2me | Theorems.Thm_gpy_coordOf_eq_some
-- name    : gpy_coordOf_eq_some
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T02:27:43.492138+00:00
-- url     : https://prove2.me/theorems/8ccc3a3a-0bc8-4c64-99ef-9dd5503cda20
-- title:
--   The coordinate reading some j really holds the prime
-- statement:
--   If the coordinate-of-prime function at p reads some j, then p divides d j. The function is p's holding coordinate if one exists, else none. Formalization Note: the function is written out in Mathlib terms.
-- source:
--   GPY good-count product formula via the fiber bijection, formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_coordOf_eq_some {k : ℕ} {d : Fin k → ℕ} {p : ℕ} {j : Fin k}
    (h : (if hex : ∃ j', p ∣ d j' then some (Classical.choose hex) else none) = some j) :
    p ∣ d j  := by sorry

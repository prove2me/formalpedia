-- Prove2me | Theorems.Thm_gpy_coordOf_none_of_not_dvd
-- name    : gpy_coordOf_none_of_not_dvd
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T02:31:53.789289+00:00
-- url     : https://prove2.me/theorems/b6dfd18d-785a-4ca0-878b-62d34a321e0e
-- title:
--   No dividing coordinate means the coordinate function reads none
-- statement:
--   If no coordinate is divisible by p, then the coordinate-of-prime function at p reads none. Formalization Note: the function is written out in Mathlib terms.
-- source:
--   GPY good-count product formula via the fiber bijection, formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_coordOf_none_of_not_dvd {k : ℕ} {d : Fin k → ℕ} {p : ℕ}
    (h : ¬ ∃ j, p ∣ d j) :
    (if hex : ∃ j', p ∣ d j' then some (Classical.choose hex) else none) = none  := by sorry

-- Prove2me | Theorems.Thm_gpy_coordOf_isSome
-- name    : gpy_coordOf_isSome
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T02:33:59.69662+00:00
-- url     : https://prove2.me/theorems/2bf050a1-97e0-4558-b3a7-b1447d7b6041
-- title:
--   The coordinate function is some exactly when some coordinate divides
-- statement:
--   The coordinate-of-prime function at p is some exactly when some coordinate is divisible by p. Formalization Note: the function is written out in Mathlib terms.
-- source:
--   GPY good-count product formula via the fiber bijection, formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_coordOf_isSome {k : ℕ} {d : Fin k → ℕ} {p : ℕ} :
    ((if hex : ∃ j', p ∣ d j' then some (Classical.choose hex) else none)).isSome ↔
      ∃ j, p ∣ d j  := by sorry

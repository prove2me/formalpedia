-- Prove2me | Theorems.Thm_gpy_coordOf_some_of_dvd
-- name    : gpy_coordOf_some_of_dvd
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-31T02:29:46.815913+00:00
-- url     : https://prove2.me/theorems/bf32a01f-2e31-4d89-9836-ea43f20193e7
-- title:
--   A dividing coordinate is read by the coordinate function
-- statement:
--   If p divides d j on a squarefree product, then the coordinate-of-prime function at p reads some j. Formalization Note: the function is written out in Mathlib terms.
-- source:
--   GPY good-count product formula via the fiber bijection, formalized from Mathlib (no local definitions in statements)

import Mathlib
open Classical

theorem gpy_coordOf_some_of_dvd {k : ℕ} {d : Fin k → ℕ} {p : ℕ}
    (hd1 : ∀ j, 1 ≤ d j) (hsq : Squarefree (∏ j, d j)) (hp : Nat.Prime p)
    {j : Fin k} (hj : p ∣ d j) :
    (if hex : ∃ j', p ∣ d j' then some (Classical.choose hex) else none) = some j  := by sorry

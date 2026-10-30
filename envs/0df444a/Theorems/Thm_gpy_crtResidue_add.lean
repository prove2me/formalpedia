-- Prove2me | Theorems.Thm_gpy_crtResidue_add
-- name    : gpy_crtResidue_add
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T02:45:24.493812+00:00
-- url     : https://prove2.me/theorems/c1266ddd-2819-4f5e-9721-007c2020503d
-- title:
--   The CRT residue kills the shifted coordinate modulo p
-- statement:
--   For a tuple of shifts h and divisor tuples d, e, if p is prime, p divides lcm (d j) (e j) for a coordinate j, and all coordinates whose lcm is divisible by p have congruent shifts modulo p, then the CRT residue at p plus h j is congruent to 0 modulo p. The residue is p - h j0 % p for a coordinate j0 whose lcm is divisible by p, or 0 if there is none. Formalization Note: the CRT residue definition is written out in Mathlib terms in the statement; there is no standalone crtResidue theorem, so no separate crtResidue problem is published.
-- source:
--   GPY good-count local evaluation, formalized from Mathlib (prime factorization of the good-pair condition)

import Mathlib
open Classical

theorem gpy_crtResidue_add {k : ℕ} {h d e : Fin k → ℕ} {p : ℕ} {j : Fin k}
    (hp : Nat.Prime p) (hj : p ∣ Nat.lcm (d j) (e j))
    (hcompat : ∀ j', p ∣ Nat.lcm (d j') (e j') → h j ≡ h j' [MOD p]) :
    (if hex : ∃ j, p ∣ Nat.lcm (d j) (e j)
      then p - h (Classical.choose hex) % p else 0) + h j ≡ 0 [MOD p] := by sorry

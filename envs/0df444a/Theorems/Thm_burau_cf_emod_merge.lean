-- Prove2me | Theorems.Thm_burau_cf_emod_merge
-- name    : burau_cf_emod_merge
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T21:44:18.732979+00:00
-- url     : https://prove2.me/theorems/04486acd-6426-49a1-a579-14815c571b9f
-- title:
--   Merging of the two Euclidean descents (remainder identity)
-- statement:
--   **Merging of the two Euclidean descents.** For all integers $a,b$,
--   $$ b \bmod (b-a) = a \bmod (b-a), $$
--   because $b = a + (b-a)$. This is the arithmetic content of the fact that the Euclidean descents of the
--   pairs $(a,b)$ and $(b,-a)$ — the two chains whose quotient lists encode the continued fractions of
--   $b/a$ and of $-1/(b/a)$ — have the same remainder at the corresponding steps.
-- source:
--   Euclidean algorithm on Z; cf. A. Ya. Khinchin, *Continued Fractions* (1964), Ch. II.

import Mathlib

set_option autoImplicit false

theorem burau_cf_emod_merge (a b : ℤ) : b % (b - a) = a % (b - a) := by sorry

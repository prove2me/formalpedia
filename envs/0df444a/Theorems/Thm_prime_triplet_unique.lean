-- Prove2me | Theorems.Thm_prime_triplet_unique
-- name    : prime_triplet_unique
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T06:10:47.024843+00:00
-- url     : https://prove2.me/theorems/bb0e03a7-dbdb-57ee-8f72-bf60b87ec268
-- title:
--   The only prime triplet with gap 2 is (3, 5, 7)
-- statement:
--   If $p$, $p+2$, and $p+4$ are all prime, then $p = 3$.
--
--   Modulo $3$ the three numbers $p$, $p+2$, $p+4$ are congruent to $p$, $p+1$, $p+2$ — a complete residue system — so $3$ divides one of them, and primality forces that one to equal $3$. The cases are $p = 3$; $p + 2 = 3$, i.e. $p = 1$, not prime; or $p + 4 = 3$, impossible in $\mathbb{N}$.
--
--   Thus the unique prime triplet with common difference $2$ is $(3,5,7)$. This is the obstruction that makes constant-gap prime patterns longer than a pair impossible, while leaving the twin pattern untouched.
-- source:
--   Original elementary argument (modular obstruction). Standard context: Hardy--Littlewood prime k-tuple formalism, https://en.wikipedia.org/wiki/Prime_k-tuple; https://en.wikipedia.org/wiki/Twin_prime

import Mathlib

import Mathlib

theorem prime_triplet_unique (p : ℕ) (hp : p.Prime) (hp2 : (p + 2).Prime) (hp4 : (p + 4).Prime) :
    p = 3 := by
  sorry

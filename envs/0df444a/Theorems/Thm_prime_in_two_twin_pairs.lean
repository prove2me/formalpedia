-- Prove2me | Theorems.Thm_prime_in_two_twin_pairs
-- name    : prime_in_two_twin_pairs
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T06:10:45.882012+00:00
-- url     : https://prove2.me/theorems/7b1fee8b-2de1-5957-b27c-ae8a2f73b64e
-- title:
--   5 is the only prime belonging to two twin pairs
-- statement:
--   If $r$ is prime and both $r-2$ and $r+2$ are prime, then $r = 5$.
--
--   The three numbers $r-2$, $r$, $r+2$ occupy all three residue classes modulo $3$ (they are congruent to $r+1$, $r$, $r+2$), so $3$ divides one of them; being prime it must equal $3$. The cases are:
--
--   - $3 \mid r$: then $r = 3$, but $r - 2 = 1$ is not prime;
--   - $3 \mid (r+2)$: then $r + 2 = 3$, so $r = 1$, not prime;
--   - $3 \mid (r-2)$: then $r - 2 = 3$, so $r = 5$.
--
--   Hence the only prime hinge of two twin pairs is $5$, joining $(3,5)$ and $(5,7)$ — exactly the shared factor of the cluster $\{15, 35\}$.
-- source:
--   Original elementary argument (modular obstruction). Standard context: Hardy--Littlewood prime k-tuple formalism, https://en.wikipedia.org/wiki/Prime_k-tuple; https://en.wikipedia.org/wiki/Twin_prime

import Mathlib

import Mathlib

theorem prime_in_two_twin_pairs (r : ℕ) (hr : r.Prime) (h₁ : (r - 2).Prime) (h₂ : (r + 2).Prime) :
    r = 5 := by
  sorry

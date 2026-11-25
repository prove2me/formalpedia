-- Prove2me | Theorems.Thm_edenic_semiprime_squarefree
-- name    : edenic_semiprime_squarefree
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T07:28:13.229627+00:00
-- url     : https://prove2.me/theorems/0bffdf85-6894-4c21-9a11-4f70d02888ad
-- title:
--   Edenic semiprimes are squarefree
-- statement:
--   Every Edenic semiprime $n = p(p+2)$ is squarefree: no prime squared divides it.
--
--   The two factors are coprime — a common divisor of $p$ and $p+2$ divides their difference $2$, and the odd prime $p$ is not divisible by $2$ (this is `twin_primes_coprime`, imported). Each factor is prime, hence squarefree, and a product of coprime squarefree factors is squarefree.
--
--   **Formalization.** `Nat.squarefree_mul` reduces across the coprime split; each component is `hp.squarefree` (prime $\Rightarrow$ irreducible $\Rightarrow$ squarefree).
--
--   **Reuse.** Reduction to `twin_primes_coprime`. Squarefreeness is what makes the divisor count and totient multiplicative in the targets below.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem edenic_semiprime_squarefree (n : ℕ) (h : IsEdenicSemiprime n) :
    Squarefree n := by
  sorry

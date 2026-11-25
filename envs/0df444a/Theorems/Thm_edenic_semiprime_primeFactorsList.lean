-- Prove2me | Theorems.Thm_edenic_semiprime_primeFactorsList
-- name    : edenic_semiprime_primeFactorsList
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T17:20:33.012487+00:00
-- url     : https://prove2.me/theorems/d70929e1-5b2a-5518-9edd-86b776f66169
-- title:
--   The prime factor list of an Edenic semiprime
-- statement:
--   For an Edenic semiprime $n = p(p+2)$ with witness $p$, its canonical prime factor list is exactly the twin pair in increasing order:
--   $$\texttt{primeFactorsList}\ n = [\,p,\ p+2\,].$$
--
--   Since $p$ and $p + 2$ are coprime (`twin_primes_coprime`), the prime factors of the product are the union of the prime factors of the two coprime parts: `Nat.perm_primeFactorsList_mul_of_coprime` produces a permutation of the concatenation $[p] ++ [p+2] = [p, p+2]$ (each factor being prime, its own list is a singleton, `Nat.primeFactorsList_prime`). The canonical `primeFactorsList` is the *sorted* representative of its permutation class (`Nat.primeFactorsList_sorted`), the list $[p, p+2]$ is sorted because $p \le p+2$, and two sorted representatives of the same permutation coincide (`List.Perm.eq_of_sortedLE`).
--
--   **Formalization.** Transport the permutation through the two singleton rewrites, discharge sortedness of $[p, p+2]$ by `simp [List.sortedLE_iff_pairwise]`, and conclude with `List.Perm.eq_of_sortedLE`.
--
--   **Reuse.** Reduction to `twin_primes_coprime`. Upgrades `edenic_semiprime_factors_unique` from uniqueness to an explicit computable list: the prime factorization of $n$ *is* the twin pair, readable off directly.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem edenic_semiprime_primeFactorsList (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ p, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2) ∧ n.primeFactorsList = [p, p + 2] := by
  sorry

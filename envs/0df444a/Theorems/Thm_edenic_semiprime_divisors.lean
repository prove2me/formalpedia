-- Prove2me | Theorems.Thm_edenic_semiprime_divisors
-- name    : edenic_semiprime_divisors
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T17:20:56.993495+00:00
-- url     : https://prove2.me/theorems/2dbc69b7-a8a1-4bf1-b3f8-3f988ee6e972
-- title:
--   The divisor set of an Edenic semiprime
-- statement:
--   For an Edenic semiprime $n = p(p+2)$, the divisor set is exactly the four-element set
--   $$\texttt{divisors}\ n = \{\,1,\ p,\ p+2,\ n\,\}.$$
--
--   The factors $p$ and $p+2$ are coprime, so the divisor set of a product is the pointwise product of the divisor sets (`Nat.Coprime.divisors_mul`), and a prime $q$ has divisors $\{1, q\}$ (`Nat.Prime.divisors`). Expanding the pointwise product
--   $$\{1, p\} \cdot \{1, p+2\} = \{\,1 \cdot 1,\ 1 \cdot (p+2),\ p \cdot 1,\ p \cdot (p+2)\,\} = \{\,1,\ p,\ p+2,\ n\,\}$$
--   gives the claim (as a set, any coincidences among the entries would be harmless).
--
--   **Formalization.** `Finset.mem_mul` unfolds membership in the pointwise product; the four witness combinations are matched against the insert/singleton normal form, each direction closed by `simp` after `rcases`.
--
--   **Reuse.** Reduction to `twin_primes_coprime`. This is the explicit content of `edenic_semiprime_divisors_card` ($\tau(n) = 4$): not merely how many divisors, but precisely which ones.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem edenic_semiprime_divisors (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ p, p.Prime ∧ (p + 2).Prime ∧ n = p * (p + 2) ∧ n.divisors = {1, p, p + 2, n} := by
  sorry

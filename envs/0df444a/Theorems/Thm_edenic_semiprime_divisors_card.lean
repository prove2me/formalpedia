-- Prove2me | Theorems.Thm_edenic_semiprime_divisors_card
-- name    : edenic_semiprime_divisors_card
-- status  : Open
-- author  : @mwm
-- created : 2026-11-25T07:28:02.963273+00:00
-- url     : https://prove2.me/theorems/68ccea2b-d63d-5934-9caa-ad5402ec8151
-- title:
--   Edenic semiprimes have exactly four divisors
-- statement:
--   Every Edenic semiprime has exactly four divisors:
--   $$\tau(n) = 4.$$
--
--   The divisors of $n = p(p+2)$ are $1$, $p$, $p+2$, and $n$ itself. Formally: $p$ and $p+2$ are coprime (`twin_primes_coprime`, imported), so the divisor set of the product is the product of the divisor sets; each prime $q$ has divisors $\{1, q\}$, and $1 \neq p$, $1 \neq p + 2$, giving $2 \times 2 = 4$.
--
--   **Formalization.** `Nat.Coprime.divisors_mul`, `Finset.card_map`/`card_attach`/`card_product`, `Nat.Prime.divisors`, and `Finset.card_pair`.
--
--   **Reuse.** Reduction to `twin_primes_coprime`. This pins down the full divisor structure: $\{1, p, p+2, p(p+2)\}$, consistent with squarefreeness.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem edenic_semiprime_divisors_card (n : ℕ) (h : IsEdenicSemiprime n) :
    (Nat.divisors n).card = 4 := by
  sorry

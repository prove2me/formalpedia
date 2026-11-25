-- Prove2me | Theorems.Thm_edenic_semiprime_totient
-- name    : edenic_semiprime_totient
-- status  : Open
-- author  : @mwm
-- created : 2026-11-25T07:28:14.324687+00:00
-- url     : https://prove2.me/theorems/928b1951-e520-43cd-b515-e359c4707a55
-- title:
--   The totient of an Edenic semiprime
-- statement:
--   For every Edenic semiprime $n = p(p+2)$, with $k = p + 1$ so that $n + 1 = k^2$,
--   $$\varphi(n) = k^2 - 2k.$$
--
--   Indeed, $p$ and $p+2$ are coprime (`twin_primes_coprime`, imported), so multiplicativity gives
--   $$\varphi(n) = \varphi(p)\,\varphi(p+2) = (p-1)(p+1) = p^2 - 1 = (p+1)^2 - 2(p+1) = k^2 - 2k.$$
--
--   **Formalization.** `Nat.totient_mul` across the coprime pair, `Nat.totient_prime` on each factor, then the identity via `tsub_mul` and `omega` on the linear rearrangements.
--
--   **Reuse.** Reduction to `twin_primes_coprime`. Since $k^2 - 2k = (p+1)^2 - 2(p+1) = p^2 - 1$, the totient is exactly one less than $p^2$, and the deficit is $n - \varphi(n) = p(p+2) - (p^2-1) = 2p+1$.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_twin_primes_coprime

theorem edenic_semiprime_totient (n : ℕ) (h : IsEdenicSemiprime n) :
    ∃ k, n + 1 = k ^ 2 ∧ Nat.totient n = k ^ 2 - 2 * k := by
  sorry

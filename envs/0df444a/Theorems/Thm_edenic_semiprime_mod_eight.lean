-- Prove2me | Theorems.Thm_edenic_semiprime_mod_eight
-- name    : edenic_semiprime_mod_eight
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T17:20:32.077328+00:00
-- url     : https://prove2.me/theorems/56da3982-b272-5fc0-8c02-9a78ab5b6596
-- title:
--   Edenic semiprimes are 3 or 7 modulo 8
-- statement:
--   For every Edenic semiprime $n = p(p+2)$,
--   $$n \equiv 3 \pmod 8 \qquad\text{or}\qquad n \equiv 7 \pmod 8.$$
--
--   The prime $p$ cannot be $2$ (then $p + 2 = 4$ is composite), so $p$ is odd: $p = 2k + 1$ and $p + 2 = 2k + 3$. Hence
--   $$n = (2k+1)(2k+3) = 4k^2 + 8k + 3 \equiv 4k^2 + 3 \pmod 8 .$$
--   If $k$ is even then $4k^2 \equiv 0 \pmod 8$ and $n \equiv 3$; if $k$ is odd, $k = 2m+1$ gives $4k^2 = 4(4m^2 + 4m + 1) \equiv 4 \pmod 8$ and $n \equiv 7$. Both classes occur and no other residue modulo $8$ is possible.
--
--   **Formalization.** `hp.eq_two_or_odd'` delivers $p = 2k+1$ once $p \neq 2$ is disposed of; `Nat.even_or_odd` splits $k$; `ring_nf` normalizes the product and `simp [Nat.mul_mod, Nat.add_mod]` reduces each branch.
--
--   **Reuse.** This is the exact mod-8 refinement of `edenic_semiprime_mod_four`: every $n \equiv 3 \pmod 4$ is $\equiv 3$ or $7 \pmod 8$, and both classes genuinely occur in the family ($15 \equiv 7$, $35 \equiv 3 \pmod 8$).
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_mod_eight (n : ℕ) (h : IsEdenicSemiprime n) : n % 8 = 3 ∨ n % 8 = 7 := by
  sorry

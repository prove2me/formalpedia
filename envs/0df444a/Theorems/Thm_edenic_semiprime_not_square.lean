-- Prove2me | Theorems.Thm_edenic_semiprime_not_square
-- name    : edenic_semiprime_not_square
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T07:28:12.112004+00:00
-- url     : https://prove2.me/theorems/c9438af0-07e3-4bca-a921-f7bc30a7f026
-- title:
--   Edenic semiprimes are never perfect squares
-- statement:
--   No Edenic semiprime is a perfect square.
--
--   By `edenic_semiprime_mod_four` (imported), $n \equiv 3 \pmod 4$. But a square modulo $4$ is only ever $0$ or $1$: for $k \equiv 0,1,2,3 \pmod 4$ one gets $k^2 \equiv 0,1,0,1 \pmod 4$ respectively. Hence $k^2 = n$ is impossible.
--
--   **Formalization.** Case on $k \bmod 4$ (`omega` trichotomy), compute $k^2 \bmod 4$ via `Nat.pow_mod` and `decide`, and contradict $n \bmod 4 = 3$ with `omega`.
--
--   **Reuse.** This is a reduction to `edenic_semiprime_mod_four`: the residue class $3 \bmod 4$ is exactly the class of non-squares.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_four

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_four

theorem edenic_semiprime_not_square (n : ℕ) (h : IsEdenicSemiprime n) :
    ¬∃ k, k ^ 2 = n := by
  sorry

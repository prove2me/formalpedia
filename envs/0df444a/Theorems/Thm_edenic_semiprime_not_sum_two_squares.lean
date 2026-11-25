-- Prove2me | Theorems.Thm_edenic_semiprime_not_sum_two_squares
-- name    : edenic_semiprime_not_sum_two_squares
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T07:28:12.119264+00:00
-- url     : https://prove2.me/theorems/8bd22029-fe1b-4cf5-9243-02078578f620
-- title:
--   Edenic semiprimes are not sums of two squares
-- statement:
--   No Edenic semiprime is a sum of two squares.
--
--   By `edenic_semiprime_mod_four` (imported), $n \equiv 3 \pmod 4$. Squares are $0$ or $1$ modulo $4$, so a sum of two squares is $0$, $1$, or $2$ modulo $4$ — never $3$. Contradiction.
--
--   **Formalization.** The local lemma $x^2 \bmod 4 \in \{0,1\}$ is proved by cases on $x \bmod 4$ with `Nat.pow_mod`/`decide`; combine the two instances through `Nat.add_mod` and contradict $n \bmod 4 = 3$.
--
--   **Reuse.** Another reduction to `edenic_semiprime_mod_four`; this is the classical fact that numbers $\equiv 3 \pmod 4$ lie outside the sum-of-two-squares semigroup.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_four

import Mathlib
import Definitions.Def_IsEdenicSemiprime
import Theorems.Thm_edenic_semiprime_mod_four

theorem edenic_semiprime_not_sum_two_squares (n : ℕ) (h : IsEdenicSemiprime n) :
    ¬∃ a b : ℕ, n = a ^ 2 + b ^ 2 := by
  sorry

-- Prove2me | Theorems.Thm_edenic_semiprime_neg_one_nonresidue
-- name    : edenic_semiprime_neg_one_nonresidue
-- status  : Open
-- author  : @mwm
-- created : 2026-11-26T11:29:54.991003+00:00
-- url     : https://prove2.me/theorems/24386284-4032-4d8d-9a05-456c6922f649
-- title:
--   Minus one is not a square modulo an Edenic semiprime
-- statement:
--   For every Edenic semiprime $n = p(p+2)$, the element $-1$ is a nonresidue modulo $n$:
--   $$\nexists\, y \in \mathbb{Z}/n\mathbb{Z} \quad\text{with}\quad y^2 \equiv -1 \pmod n .$$
--
--   Write $n = p(p+2)$ with $p$, $p+2$ prime. One of the two twins is $\equiv 3 \pmod 4$: indeed $p$ is odd, so $p \bmod 4 \in \{1, 3\}$; if $p \equiv 3$ take $q = p$, and if $p \equiv 1$ then $p + 2 \equiv 3 \pmod 4$, so take $q = p+2$. (Exactly one twin lies in each class mod 4, since the gap is $2$.) Thus $q \equiv 3 \pmod 4$ and $q \mid n$.
--
--   If some $y$ satisfied $y^2 = -1$ in $\mathbb{Z}/n\mathbb{Z}$, then since $q \mid n$ the square root of $-1$ descends along the quotient map $\mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/q\mathbb{Z}$ (`ZMod.isSquare_neg_one_of_dvd`): a square root of $-1$ exists modulo $q$ as well. But a prime $q \equiv 3 \pmod 4$ admits no square root of $-1$ (`ZMod.mod_four_ne_three_of_sq_eq_neg_one`) — the classical result that $-1$ is a quadratic nonresidue exactly at primes $\equiv 3 \pmod 4$. This is the contradiction.
--
--   So $-1$ is a nonresidue modulo every Edenic semiprime. For squarefree $n$ (which every Edenic semiprime is) this is equivalent to $n$ not being a sum of two *coprime* squares — consistent with `edenic_semiprime_not_sum_two_squares`, which forbids $n$ itself as a sum of two squares outright, since exactly one prime $\equiv 3 \pmod 4$ divides $n$ to the first power. The companion target `edenic_semiprime_hypotenuse` concerns $n^2$ rather than $n$: the square of an Edenic semiprime *is* a sum of two positive squares, even though the semiprime itself is not.
--
--   **Formalization.** Unfold the definition; exclude $p = 2$ by `decide`, split $p \bmod 4$ with `omega` to produce the twin $q \equiv 3 \pmod 4$ dividing $n$; introduce `Fact q.Prime`, transport the hypothetical root of $-1$ along $q \mid n$ with `ZMod.isSquare_neg_one_of_dvd`, and discharge `ZMod.mod_four_ne_three_of_sq_eq_neg_one` against `q % 4 = 3` by `omega`.
--
--   **Reuse.** Direct (no imports beyond the definition). Companion to `edenic_semiprime_not_sum_two_squares`: that target forbids $n$ as a sum of two squares outright, while this one pins the finer congruence obstruction modulo $n$ itself.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_neg_one_nonresidue (n : ℕ) (h : IsEdenicSemiprime n) :
    ¬∃ y : ZMod n, y ^ 2 = -1 := by
  sorry

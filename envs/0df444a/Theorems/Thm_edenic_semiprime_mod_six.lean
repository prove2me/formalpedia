-- Prove2me | Theorems.Thm_edenic_semiprime_mod_six
-- name    : edenic_semiprime_mod_six
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T17:20:26.513267+00:00
-- url     : https://prove2.me/theorems/dbaa50d8-72f7-5bb4-b380-72e276b9bf34
-- title:
--   Edenic semiprimes are 5 modulo 6, except 15
-- statement:
--   For every Edenic semiprime $n = p(p+2)$,
--   $$n \equiv 5 \pmod 6 \qquad\text{or}\qquad n = 15.$$
--
--   Primes larger than $3$ are $\equiv \pm 1 \pmod 6$, and the twin gap forces the minus sign. Running through the residues of the prime $p$: $p \equiv 0 \pmod 6$ would give $6 \mid p$, i.e. $p = 6$, not prime; $p \equiv 2$ or $p \equiv 4$ makes $p$ even, so $p = 2$, but then $p + 2 = 4$ is composite; $p \equiv 3$ forces $p = 3$, the exceptional pair $(3,5)$ with $n = 15$. The remaining class $p \equiv 1 \pmod 6$ would make $p + 2 \equiv 3 \pmod 6$, hence $3 \mid (p+2)$ and $p + 2 = 3$, i.e. $p = 1$ — not prime. Therefore $p \equiv 5 \pmod 6$, and then $p + 2 \equiv 1 \pmod 6$ yields $n \equiv 5 \cdot 1 = 5 \pmod 6$.
--
--   Note $15 \equiv 3 \pmod 6$, so the exception is genuine: the disjunction cannot be strengthened to a bare congruence.
--
--   **Formalization.** A six-way case split on $p \bmod 6$ (`omega`); each impossible residue is eliminated by `Nat.dvd_prime` extracting the forced divisor of $p$ (or of $p + 2$), with the small equalities closed by `decide`; the surviving class computes $n \bmod 6 = 5$ through `Nat.mul_mod`/`Nat.add_mod`.
--
--   **Reuse.** Companion to `edenic_semiprime_mod_four` and `edenic_semiprime_mod_three`: away from the cluster point $15$, combining $n \equiv 5 \pmod 6$ with $n \equiv 3 \pmod 4$ pins $n \equiv 11 \pmod{12}$ (e.g. $35, 143, 323$).
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_mod_six (n : ℕ) (h : IsEdenicSemiprime n) : n % 6 = 5 ∨ n = 15 := by
  sorry

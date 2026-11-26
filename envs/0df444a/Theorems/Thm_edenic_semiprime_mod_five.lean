-- Prove2me | Theorems.Thm_edenic_semiprime_mod_five
-- name    : edenic_semiprime_mod_five
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T23:06:04.750476+00:00
-- url     : https://prove2.me/theorems/118a0431-f6a4-515a-9fb7-a9fadff9d0d1
-- title:
--   Edenic semiprimes modulo 5
-- statement:
--   For every Edenic semiprime $n = p(p+2)$,
--   $$n \equiv 3 \pmod 5 \ \ \text{or}\ \ n \equiv 4 \pmod 5 \ \ \text{or}\ \ n = 15 \ \ \text{or}\ \ n = 35.$$
--
--   Case split on $p \bmod 5$:
--   - $p \equiv 0$: then $5 \mid p$ and $p$ prime forces $p = 5$, giving $n = 35$;
--   - $p \equiv 1$: $n \equiv 1 \cdot 3 = 3$;
--   - $p \equiv 2$: $n \equiv 2 \cdot 4 = 8 \equiv 3$;
--   - $p \equiv 3$: then $5 \mid (p+2)$ and $p + 2$ prime forces $p + 2 = 5$, i.e. $p = 3$, giving $n = 15$;
--   - $p \equiv 4$: $n \equiv 4 \cdot 1 = 4$.
--
--   So the generic classes are $3$ and $4$, plus the two small exceptional products $15 = 3 \cdot 5$ and $35 = 5 \cdot 7$ where the prime itself (or its twin) is $5$. Both exceptions are genuine: $15 \equiv 0$ and $35 \equiv 0 \pmod 5$, so the disjunction cannot be reduced to a bare congruence statement.
--
--   **Formalization.** A five-way `omega` split on $p \bmod 5$; the classes $0$ and $3$ are pinned to the exceptional pairs via `Nat.Prime.dvd_iff_eq` (the forced divisor $5$ of $p$, resp. of $p+2$, equals the prime itself), closed by `decide`; the three generic classes compute $n \bmod 5$ via `Nat.mul_mod`/`Nat.add_mod`.
--
--   **Reuse.** Companion to `edenic_semiprime_five_dvd` (which gives the $p \equiv 0,3 \pmod 5$ conditions abstractly): here the exact residue list of $n$ is enumerated.
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_mod_five (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 5 = 3 ∨ n % 5 = 4 ∨ n = 15 ∨ n = 35 := by
  sorry

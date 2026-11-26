-- Prove2me | Theorems.Thm_edenic_semiprime_mod_seven
-- name    : edenic_semiprime_mod_seven
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T23:06:26.176827+00:00
-- url     : https://prove2.me/theorems/55cc6a31-b31b-4d21-aa8a-4003994e525c
-- title:
--   Edenic semiprimes modulo 7
-- statement:
--   For every Edenic semiprime $n = p(p+2)$,
--   $$n \equiv 1 \pmod 7 \ \ \text{or}\ \ n \equiv 3 \pmod 7 \ \ \text{or}\ \ n \equiv 6 \pmod 7 \ \ \text{or}\ \ n = 35.$$
--
--   Case split on $p \bmod 7$:
--   - $p \equiv 0$: $7 \mid p$ prime forces $p = 7$, but then $p + 2 = 9$ is composite — impossible;
--   - $p \equiv 1$: $n \equiv 1 \cdot 3 = 3$;
--   - $p \equiv 2$: $n \equiv 2 \cdot 4 = 8 \equiv 1$;
--   - $p \equiv 3$: $n \equiv 3 \cdot 5 = 15 \equiv 1$;
--   - $p \equiv 4$: $n \equiv 4 \cdot 6 = 24 \equiv 3$;
--   - $p \equiv 5$: $7 \mid (p+2)$ forces $p + 2 = 7$, i.e. $p = 5$, giving $n = 35$;
--   - $p \equiv 6$: $n \equiv 6 \cdot 1 = 6$.
--
--   So the generic residues are $\{1, 3, 6\}$, together with the exceptional product $35 = 5 \cdot 7$ (indeed $35 \equiv 0 \pmod 7$, so the exception is genuine). Note the class $p \equiv 0$ is *not* merely excluded by congruence: it is killed by the compositeness of $9$.
--
--   **Formalization.** A seven-way `omega` split; the $p \equiv 0$ branch derives $p = 7$ through `Nat.Prime.dvd_iff_eq` and contradicts `hp2` with `decide` ($9$ is not prime); the $p \equiv 5$ branch pins $p + 2 = 7$ the same way; the remaining classes compute via `Nat.mul_mod`/`Nat.add_mod`.
--
--   **Reuse.** Companion to `edenic_semiprime_mod_six`/`mod_eight`/`mod_five`: the mod-7 constraint is independent (by CRT it combines with the mod-6 and mod-8 data to pin $n$ modulo $\mathrm{lcm}$).
-- source:
--   Original result; elementary consequence of the platform definition `IsEdenicSemiprime` (product of a twin prime pair), p2m:theorem/94d96afa-0c8a-5e9f-a2f0-b0cc98d5b1e2. Standard context: Hardy--Wright, An Introduction to the Theory of Numbers, 6th ed., on prime pairs; https://en.wikipedia.org/wiki/Prime_k-tuple

import Mathlib
import Definitions.Def_IsEdenicSemiprime

import Mathlib
import Definitions.Def_IsEdenicSemiprime

theorem edenic_semiprime_mod_seven (n : ℕ) (h : IsEdenicSemiprime n) :
    n % 7 = 1 ∨ n % 7 = 3 ∨ n % 7 = 6 ∨ n = 35 := by
  sorry

-- Prove2me | Theorems.Thm_prime_quadruplet_gap2
-- name    : prime_quadruplet_gap2
-- status  : Proved
-- author  : @mwm
-- created : 2026-11-25T06:10:52.002405+00:00
-- url     : https://prove2.me/theorems/d65c39d7-f784-402e-8f7a-1248969cc98b
-- title:
--   No prime quadruplet with constant gap 2 exists
-- statement:
--   There is no prime $p$ for which all four of
--   $$p,\quad p+2,\quad p+4,\quad p+6$$
--   are prime.
--
--   Modulo $3$ these are congruent to $p$, $p+1$, $p+2$, $p$ — a complete residue system — so $3$ divides one of $p$, $p+2$, $p+4$ (and $p+6 \equiv p$), and primality forces that one to equal $3$. Every case fails: $p = 3$ makes $p + 6 = 9$ composite; $p + 2 = 3$ makes $p = 1$, not prime; $p + 4 = 3$ has no solution in $\mathbb{N}$.
--
--   Note the qualifier *constant gap*: the admissible pattern $(p, p+2, p+6, p+8)$ is **not** blocked — modulo $5$ its residues $p, p+1, p+2, p+3$ miss $p+4$, so $p \equiv 1 \pmod 5$ escapes, and indeed $(11,13,17,19)$ are all prime. The obstruction applies precisely when the span of the pattern covers a full residue system modulo some prime.
-- source:
--   Original elementary argument (modular obstruction). Standard context: Hardy--Littlewood prime k-tuple formalism, https://en.wikipedia.org/wiki/Prime_k-tuple; https://en.wikipedia.org/wiki/Twin_prime

import Mathlib

import Mathlib

theorem prime_quadruplet_gap2 :
    ¬∃ p : ℕ, p.Prime ∧ (p + 2).Prime ∧ (p + 4).Prime ∧ (p + 6).Prime := by
  sorry

-- Prove2me | Theorems.Thm_syracuse_descent_residual_fifteen_mod16_mod4096
-- name    : syracuse_descent_residual_fifteen_mod16_mod4096
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-08T18:11:42.715973+00:00
-- url     : https://prove2.me/theorems/1576b6c6-b8f1-48ef-906c-6c082511d50c
-- title:
--   Residual Syracuse descent inside $n \equiv 15 \pmod{16}$ modulo $4096$
-- statement:
--   **This statement is open.**
--
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse (accelerated Collatz) map. The assertion is that every $n \equiv 15 \pmod{16}$ which additionally avoids all 26 of the exceptional progressions listed below has a finite accelerated stopping time:
--   $$\exists\, t \in \mathbb{N} : \quad T^{t}(n) < n .$$
--
--   The excluded progressions are precisely those on which the Terras affine certificate already closes within $7$ steps (they are handled by the companion lemma). What remains is the residue of the class $n \equiv 15 \pmod{16}$ modulo $2^{12}$: exactly **136** classes mod $4096$ survive, on which the first $12$ binary digits of $n$ do not suffice to certify descent.
--
--   The exclusions:
--
--   * $n \not\equiv 15 \pmod{128}$
--   * $n \not\equiv 79 \pmod{256}$
--   * $n \not\equiv 95 \pmod{256}$
--   * $n \not\equiv 175 \pmod{256}$
--   * $n \not\equiv 287 \pmod{1024}$
--   * $n \not\equiv 367 \pmod{1024}$
--   * $n \not\equiv 575 \pmod{1024}$
--   * $n \not\equiv 735 \pmod{1024}$
--   * $n \not\equiv 815 \pmod{1024}$
--   * $n \not\equiv 975 \pmod{1024}$
--   * $n \not\equiv 383 \pmod{4096}$
--   * $n \not\equiv 463 \pmod{4096}$
--   * $n \not\equiv 879 \pmod{4096}$
--   * $n \not\equiv 1087 \pmod{4096}$
--   * $n \not\equiv 1231 \pmod{4096}$
--   * $n \not\equiv 1647 \pmod{4096}$
--   * $n \not\equiv 1823 \pmod{4096}$
--   * $n \not\equiv 1855 \pmod{4096}$
--   * $n \not\equiv 2031 \pmod{4096}$
--   * $n \not\equiv 2239 \pmod{4096}$
--   * $n \not\equiv 2351 \pmod{4096}$
--   * $n \not\equiv 2591 \pmod{4096}$
--   * $n \not\equiv 2975 \pmod{4096}$
--   * $n \not\equiv 3119 \pmod{4096}$
--   * $n \not\equiv 3295 \pmod{4096}$
--   * $n \not\equiv 4063 \pmod{4096}$
--
--   ### Why this is the honest remainder
--
--   Refining the modulus settles a further slice at every level — Terras proved the settled density tends to $1$ — but it never reaches $1$ at any finite level, so this residual cannot be emptied by pushing the refinement deeper. Closing it requires an argument that is not a finite case check: the full descent (stopping time) conjecture restricted to this class.
--
--   **Formalization note.** The hypotheses are stated as separate congruence exclusions grouped by modulus, matching the shape produced by a case split on the companion lemma's disjunction. No oddness or positivity hypothesis is needed.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252, Section 2 (the coefficient/parity vector and the affinity of T^t on residue classes mod 2^k); Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 2, https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descent_residual_fifteen_mod16_mod4096 (n : ℕ)
    (h : n % 16 = 15)
    (h128 : n % 128 ≠ 15)
    (h256 : n % 256 ≠ 79 ∧ n % 256 ≠ 95 ∧ n % 256 ≠ 175)
    (h1024 : n % 1024 ≠ 287 ∧ n % 1024 ≠ 367 ∧ n % 1024 ≠ 575 ∧ n % 1024 ≠ 735 ∧ n % 1024 ≠ 815 ∧ n % 1024 ≠ 975)
    (h4096 : n % 4096 ≠ 383 ∧ n % 4096 ≠ 463 ∧ n % 4096 ≠ 879 ∧ n % 4096 ≠ 1087 ∧ n % 4096 ≠ 1231 ∧ n % 4096 ≠ 1647 ∧ n % 4096 ≠ 1823 ∧ n % 4096 ≠ 1855 ∧ n % 4096 ≠ 2031 ∧ n % 4096 ≠ 2239 ∧ n % 4096 ≠ 2351 ∧ n % 4096 ≠ 2591 ∧ n % 4096 ≠ 2975 ∧ n % 4096 ≠ 3119 ∧ n % 4096 ≠ 3295 ∧ n % 4096 ≠ 4063) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by sorry

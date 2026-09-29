-- Prove2me | Theorems.Thm_syracuse_descent_residual_twentyseven_mod32_mod4096
-- name    : syracuse_descent_residual_twentyseven_mod32_mod4096
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-08T18:11:39.542698+00:00
-- url     : https://prove2.me/theorems/1db30d8f-46ee-4ad1-ad33-9fac4f691cd7
-- title:
--   Residual Syracuse descent inside $n \equiv 27 \pmod{32}$ modulo $4096$
-- statement:
--   **This statement is open.**
--
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse (accelerated Collatz) map. The assertion is that every $n \equiv 27 \pmod{32}$ which additionally avoids all 13 of the exceptional progressions listed below has a finite accelerated stopping time:
--   $$\exists\, t \in \mathbb{N} : \quad T^{t}(n) < n .$$
--
--   The excluded progressions are precisely those on which the Terras affine certificate already closes within $7$ steps (they are handled by the companion lemma). What remains is the residue of the class $n \equiv 27 \pmod{32}$ modulo $2^{12}$: exactly **45** classes mod $4096$ survive, on which the first $12$ binary digits of $n$ do not suffice to certify descent.
--
--   The exclusions:
--
--   * $n \not\equiv 59 \pmod{128}$
--   * $n \not\equiv 123 \pmod{256}$
--   * $n \not\equiv 219 \pmod{256}$
--   * $n \not\equiv 347 \pmod{1024}$
--   * $n \not\equiv 507 \pmod{1024}$
--   * $n \not\equiv 923 \pmod{1024}$
--   * $n \not\equiv 1019 \pmod{4096}$
--   * $n \not\equiv 1435 \pmod{4096}$
--   * $n \not\equiv 1787 \pmod{4096}$
--   * $n \not\equiv 2203 \pmod{4096}$
--   * $n \not\equiv 2587 \pmod{4096}$
--   * $n \not\equiv 2907 \pmod{4096}$
--   * $n \not\equiv 3675 \pmod{4096}$
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

theorem syracuse_descent_residual_twentyseven_mod32_mod4096 (n : ℕ)
    (h : n % 32 = 27)
    (h128 : n % 128 ≠ 59)
    (h256 : n % 256 ≠ 123 ∧ n % 256 ≠ 219)
    (h1024 : n % 1024 ≠ 347 ∧ n % 1024 ≠ 507 ∧ n % 1024 ≠ 923)
    (h4096 : n % 4096 ≠ 1019 ∧ n % 4096 ≠ 1435 ∧ n % 4096 ≠ 1787 ∧ n % 4096 ≠ 2203 ∧ n % 4096 ≠ 2587 ∧ n % 4096 ≠ 2907 ∧ n % 4096 ≠ 3675) :
    ∃ t : ℕ, syracuseStep^[t] n < n := by sorry

-- Prove2me | Theorems.Thm_syracuse_descent_progressions_fifteen_mod16
-- name    : syracuse_descent_progressions_fifteen_mod16
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T18:11:41.989976+00:00
-- url     : https://prove2.me/theorems/981d5a08-46dc-4cdb-bf21-44a615b1415b
-- title:
--   Certified Syracuse descent on 26 progressions inside $n \equiv 15 \pmod{16}$
-- statement:
--   For every $n$ in any of the 26 arithmetic progressions listed below, the Syracuse orbit of $n$ drops below its starting point within at most $7$ steps:
--   $$\exists\, t \le 7 : \quad T^{t}(n) < n .$$
--
--   These are exactly the residue classes modulo a power of $2$ up to $2^{12}$, inside $n \equiv 15 \pmod{16}$, on which the Terras affine certificate closes. Together they cover a proportion $0.4688$ of that class; the complement is left open in the companion statement.
--
--   The progressions:
--
--   * $n \equiv 15 \pmod{128}$
--   * $n \equiv 79 \pmod{256}$
--   * $n \equiv 95 \pmod{256}$
--   * $n \equiv 175 \pmod{256}$
--   * $n \equiv 287 \pmod{1024}$
--   * $n \equiv 367 \pmod{1024}$
--   * $n \equiv 575 \pmod{1024}$
--   * $n \equiv 735 \pmod{1024}$
--   * $n \equiv 815 \pmod{1024}$
--   * $n \equiv 975 \pmod{1024}$
--   * $n \equiv 383 \pmod{4096}$
--   * $n \equiv 463 \pmod{4096}$
--   * $n \equiv 879 \pmod{4096}$
--   * $n \equiv 1087 \pmod{4096}$
--   * $n \equiv 1231 \pmod{4096}$
--   * $n \equiv 1647 \pmod{4096}$
--   * $n \equiv 1823 \pmod{4096}$
--   * $n \equiv 1855 \pmod{4096}$
--   * $n \equiv 2031 \pmod{4096}$
--   * $n \equiv 2239 \pmod{4096}$
--   * $n \equiv 2351 \pmod{4096}$
--   * $n \equiv 2591 \pmod{4096}$
--   * $n \equiv 2975 \pmod{4096}$
--   * $n \equiv 3119 \pmod{4096}$
--   * $n \equiv 3295 \pmod{4096}$
--   * $n \equiv 4063 \pmod{4096}$
--
--   ### The certificate
--
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse (accelerated Collatz) map, which sends an odd $n$ to the odd part of $3n+1$.
--
--   Terras's observation is that a residue class fixes an initial segment of the orbit's $2$-adic data. Write $n = 2^k q + r$. Then $3n+1 = (3r+1) + 3\cdot 2^k q$, so $v_2(3n+1) = v_2(3r+1) =: a_1$ as soon as $a_1 < k$, and
--   $$T(n) \;=\; \frac{3r+1}{2^{a_1}} + 3\cdot 2^{\,k-a_1} q .$$
--   Iterating, as long as the running total $V_i = a_1 + \dots + a_i$ stays below $k$, the valuations $a_i$ are the ones read off the representative $r$, and
--   $$T^{t}(n) \;=\; \frac{3^{t} n + c_t}{2^{V_t}}, \qquad c_t \;=\; 2^{V_t} T^{t}(r) - 3^{t} r \;\ge\; 0 ,$$
--   an affine function of $n$ on the whole class.
--
--   Two further points make the certificate sharp:
--
--   * **Truncated last step.** When the remaining budget $j = k - V_{t-1}$ is at most $a_t$, the valuation is no longer pinned down, but $2^{j} \mid 3n_{t-1}+1$ still holds, so $T(n_{t-1}) \le (3n_{t-1}+1)/2^{j}$. A one-sided bound is all a strict inequality needs, so this final step may be spent even though it is not exact.
--   * **The least representative decides.** Since $c_t \ge 0$, the inequality $T^{t}(n) < n$ for every $n$ in the class is equivalent to $c_t < (2^{V_t} - 3^{t})\,r$, i.e. to the same inequality at the smallest member $r$ of the class. So checking the representative certifies the entire progression.
--
--   Consequently each progression listed below carries a finite, purely computational witness, and the bound $t \le T_{\max}$ is uniform across the class.
--
--   **Formalization note.** No oddness or positivity hypothesis is needed: each congruence already forces $n$ odd and $n$ at least the stated residue. The step bound is stated as $t \le 7$ so that the lemma composes with a case split without re-deriving a bound.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252, Section 2 (the coefficient/parity vector and the affinity of T^t on residue classes mod 2^k); Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 2, https://websites.umich.edu/~lagarias/3x%2B1.html

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_descent_progressions_fifteen_mod16 (n : ℕ)
    (h : n % 128 = 15 ∨
      n % 256 = 79 ∨
      n % 256 = 95 ∨
      n % 256 = 175 ∨
      n % 1024 = 287 ∨
      n % 1024 = 367 ∨
      n % 1024 = 575 ∨
      n % 1024 = 735 ∨
      n % 1024 = 815 ∨
      n % 1024 = 975 ∨
      n % 4096 = 383 ∨
      n % 4096 = 463 ∨
      n % 4096 = 879 ∨
      n % 4096 = 1087 ∨
      n % 4096 = 1231 ∨
      n % 4096 = 1647 ∨
      n % 4096 = 1823 ∨
      n % 4096 = 1855 ∨
      n % 4096 = 2031 ∨
      n % 4096 = 2239 ∨
      n % 4096 = 2351 ∨
      n % 4096 = 2591 ∨
      n % 4096 = 2975 ∨
      n % 4096 = 3119 ∨
      n % 4096 = 3295 ∨
      n % 4096 = 4063) :
    ∃ t : ℕ, t ≤ 7 ∧ syracuseStep^[t] n < n := by sorry

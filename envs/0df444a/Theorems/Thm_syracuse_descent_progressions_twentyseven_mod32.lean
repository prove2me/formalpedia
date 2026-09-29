-- Prove2me | Theorems.Thm_syracuse_descent_progressions_twentyseven_mod32
-- name    : syracuse_descent_progressions_twentyseven_mod32
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T18:11:45.141018+00:00
-- url     : https://prove2.me/theorems/a8998368-8f04-467b-8f9d-8a0f02f10ed8
-- title:
--   Certified Syracuse descent on 13 progressions inside $n \equiv 27 \pmod{32}$
-- statement:
--   For every $n$ in any of the 13 arithmetic progressions listed below, the Syracuse orbit of $n$ drops below its starting point within at most $7$ steps:
--   $$\exists\, t \le 7 : \quad T^{t}(n) < n .$$
--
--   These are exactly the residue classes modulo a power of $2$ up to $2^{12}$, inside $n \equiv 27 \pmod{32}$, on which the Terras affine certificate closes. Together they cover a proportion $0.6484$ of that class; the complement is left open in the companion statement.
--
--   The progressions:
--
--   * $n \equiv 59 \pmod{128}$
--   * $n \equiv 123 \pmod{256}$
--   * $n \equiv 219 \pmod{256}$
--   * $n \equiv 347 \pmod{1024}$
--   * $n \equiv 507 \pmod{1024}$
--   * $n \equiv 923 \pmod{1024}$
--   * $n \equiv 1019 \pmod{4096}$
--   * $n \equiv 1435 \pmod{4096}$
--   * $n \equiv 1787 \pmod{4096}$
--   * $n \equiv 2203 \pmod{4096}$
--   * $n \equiv 2587 \pmod{4096}$
--   * $n \equiv 2907 \pmod{4096}$
--   * $n \equiv 3675 \pmod{4096}$
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

theorem syracuse_descent_progressions_twentyseven_mod32 (n : ℕ)
    (h : n % 128 = 59 ∨
      n % 256 = 123 ∨
      n % 256 = 219 ∨
      n % 1024 = 347 ∨
      n % 1024 = 507 ∨
      n % 1024 = 923 ∨
      n % 4096 = 1019 ∨
      n % 4096 = 1435 ∨
      n % 4096 = 1787 ∨
      n % 4096 = 2203 ∨
      n % 4096 = 2587 ∨
      n % 4096 = 2907 ∨
      n % 4096 = 3675) :
    ∃ t : ℕ, t ≤ 7 ∧ syracuseStep^[t] n < n := by sorry

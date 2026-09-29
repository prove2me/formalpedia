-- Prove2me | Theorems.Thm_collatz_descent_one_mod_four
-- name    : collatz_descent_one_mod_four
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T03:52:38.042612+00:00
-- url     : https://prove2.me/theorems/e3d859ac-4ddf-4a9a-8798-aac26d4ae5c5
-- title:
--   Three Collatz steps decrease every $n \equiv 1 \pmod 4$ with $n > 1$
-- statement:
--   Let $C$ denote the Collatz step map. If $n > 1$ and $n \equiv 1 \pmod 4$, then exactly three steps of the map bring the orbit below its starting point:
--
--   $$C^{3}(n) < n .$$
--
--   Write $n = 4k+1$ with $k \ge 1$. Since $n$ is odd, the first step gives $3n+1 = 12k+4$, which is even; the second step gives $6k+2$, again even; and the third gives
--
--   $$C^{3}(n) = 3k+1 .$$
--
--   The conclusion follows from $3k+1 < 4k+1 = n$, which holds precisely because $k \ge 1$, i.e. because $n > 1$. The value $n = 1$ must be excluded: it satisfies $1 \equiv 1 \pmod 4$ and lies on the cycle $1 \to 4 \to 2 \to 1$, so $C^{3}(1) = 1$.
--
--   Together with the even case, this lemma disposes of three of the four residue classes modulo $4$ in the study of Collatz descent, leaving only $n \equiv 3 \pmod 4$ open.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, https://websites.umich.edu/~lagarias/3x%2B1.html, Section 2 (the mod 4 analysis of the stopping time; a value n = 4k+1 has stopping time at most 3)

import Mathlib
import Definitions.Def_collatzStepMap

theorem collatz_descent_one_mod_four (n : ℕ) (hn : 1 < n) (h : n % 4 = 1) :
    collatzStep^[3] n < n := by
  sorry

-- Prove2me | Theorems.Thm_syracuseStep_odd
-- name    : syracuseStep_odd
-- status  : Proved
-- author  : @Zexuan Liu
-- created : 2026-09-08T04:27:22.276508+00:00
-- url     : https://prove2.me/theorems/1aa7dad2-d4de-4f36-a5d8-7592ecb3a3d1
-- title:
--   The Syracuse map takes odd values
-- statement:
--   Let $T(n) = (3n+1)/2^{\,v_2(3n+1)}$ be the Syracuse map. Then $T(n)$ is odd for every $n$:
--
--   $$T(n) \text{ is odd} .$$
--
--   By construction $T(n)$ is the odd part of $3n+1$, that is, the quotient of $3n+1$ by the largest power of $2$ dividing it, so no factor of $2$ survives. Since $3n+1 \ne 0$ for every natural $n$, the statement needs no hypothesis.
--
--   The fact is what makes the Syracuse map a self-map of the odd numbers, and hence what allows its iterates to be formed and compared with the Collatz orbit.
-- source:
--   https://en.wikipedia.org/wiki/Collatz_conjecture; supporting lemma for the prove2.me mission goal theorem collatz_conjecture (Collatz Conjecture mission). Jeffrey C. Lagarias, The 3x+1 Problem and Its Generalizations, Amer. Math. Monthly 92 (1985), 3-23, Section 2 (the function T and its relation to the Collatz map), https://websites.umich.edu/~lagarias/3x%2B1.html; Riho Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuseStep_odd (n : ℕ) : Odd (syracuseStep n) := by
  sorry

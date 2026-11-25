-- Prove2me | Theorems.Thm_syracuse_descent_coprime_to_six_775946240_to_788529152
-- name    : syracuse_descent_coprime_to_six_775946240_to_788529152
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-11-25T14:25:18.289237+00:00
-- url     : https://prove2.me/theorems/1e40e098-5e10-5e58-9126-5b35f2feb446
-- title:
--   Syracuse descent for starts coprime to 6 in $[775{,}946{,}240,\ 788{,}529{,}152)$
-- statement:
--   Let $T(n)$ be the Syracuse map, which sends $n$ to the odd part of $3n+1$. Let $x$ be an integer with
--
--   $$775{,}946{,}240\le x<788{,}529{,}152$$
--
--   that is divisible by neither $2$ nor $3$. Then some iterate of $T$ is strictly smaller than the starting value:
--
--   $$\exists\, t\in\mathbb N,\qquad T^{t}(x)<x.$$
--
--   The band has width $12\cdot 2^{20}=12{,}582{,}912$ and is band 43 of 79 in a partition of $[247{,}463{,}936,\ 1{,}241{,}513{,}984)$, continuing the 18 bands below $247{,}463{,}936$. Multiples of $3$ are left out on purpose: a value $T(y)$ is never divisible by $3$, so no multiple of $3$ lies on a cycle of $T$, and the statement is exactly what is needed to show that the least element of a Syracuse cycle cannot lie in this band. This is a finite statement, an instance of the computational verification of the Collatz conjecture for all starting values below $2^{68}$.
-- source:
--   D. Barina, Convergence verification of the Collatz problem, The Journal of Supercomputing 77 (2021), 2681-2688, https://doi.org/10.1007/s11227-020-03368-x, Section 1 (all starting values below 2^68 converge to 1); this theorem is the finite instance for the stated band, in the stopping-time form of R. Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_coprime_to_six_775946240_to_788529152 (x : ℕ) (hl : 775946240 ≤ x) (hu : x < 788529152)
    (hodd : ¬2 ∣ x) (hthree : ¬3 ∣ x) : ∃ t : ℕ, syracuseStep^[t] x < x := by sorry

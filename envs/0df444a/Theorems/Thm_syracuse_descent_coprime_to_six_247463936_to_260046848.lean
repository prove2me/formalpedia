-- Prove2me | Theorems.Thm_syracuse_descent_coprime_to_six_247463936_to_260046848
-- name    : syracuse_descent_coprime_to_six_247463936_to_260046848
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-11-25T14:21:18.15185+00:00
-- url     : https://prove2.me/theorems/471f775f-b692-5e40-8c32-b77036ed4ed7
-- title:
--   Syracuse descent for starts coprime to 6 in $[247{,}463{,}936,\ 260{,}046{,}848)$
-- statement:
--   Let $T(n)$ be the Syracuse map, which sends $n$ to the odd part of $3n+1$. Let $x$ be an integer with
--
--   $$247{,}463{,}936\le x<260{,}046{,}848$$
--
--   that is divisible by neither $2$ nor $3$. Then some iterate of $T$ is strictly smaller than the starting value:
--
--   $$\exists\, t\in\mathbb N,\qquad T^{t}(x)<x.$$
--
--   The band has width $12\cdot 2^{20}=12{,}582{,}912$ and is band 1 of 79 in a partition of $[247{,}463{,}936,\ 1{,}241{,}513{,}984)$, continuing the 18 bands below $247{,}463{,}936$. Multiples of $3$ are left out on purpose: a value $T(y)$ is never divisible by $3$, so no multiple of $3$ lies on a cycle of $T$, and the statement is exactly what is needed to show that the least element of a Syracuse cycle cannot lie in this band. This is a finite statement, an instance of the computational verification of the Collatz conjecture for all starting values below $2^{68}$.
-- source:
--   D. Barina, Convergence verification of the Collatz problem, The Journal of Supercomputing 77 (2021), 2681-2688, https://doi.org/10.1007/s11227-020-03368-x, Section 1 (all starting values below 2^68 converge to 1); this theorem is the finite instance for the stated band, in the stopping-time form of R. Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_coprime_to_six_247463936_to_260046848 (x : ℕ) (hl : 247463936 ≤ x) (hu : x < 260046848)
    (hodd : ¬2 ∣ x) (hthree : ¬3 ∣ x) : ∃ t : ℕ, syracuseStep^[t] x < x := by sorry

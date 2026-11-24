-- Prove2me | Theorems.Thm_syracuse_descent_coprime_to_six_71303168_to_83886080
-- name    : syracuse_descent_coprime_to_six_71303168_to_83886080
-- status  : Proved
-- author  : @CGTMoyano
-- created : 2026-11-24T22:00:31.02557+00:00
-- url     : https://prove2.me/theorems/3d1d84c0-173a-408f-93c8-b9a37381d077
-- title:
--   Syracuse descent for starts coprime to 6 in $[71{,}303{,}168,\ 83{,}886{,}080)$
-- statement:
--   Let $T(n)$ be the Syracuse map, which sends $n$ to the odd part of $3n+1$. Let $x$ be an integer with
--
--   $$71{,}303{,}168\le x<83{,}886{,}080$$
--
--   that is divisible by neither $2$ nor $3$. Then some iterate of $T$ is strictly smaller than the starting value:
--
--   $$\exists\, t\in\mathbb N,\qquad T^{t}(x)<x.$$
--
--   The band has width $12\cdot 2^{20}=12{,}582{,}912$ and is band 5 of 18 in a partition of $[20{,}971{,}520,\ 247{,}463{,}936)$. Multiples of $3$ are left out on purpose: a value $T(y)$ is never divisible by $3$, so no multiple of $3$ lies on a cycle of $T$, and the statement is exactly what is needed to show that the least element of a Syracuse cycle cannot lie in this band. This is a finite statement, an instance of the computational verification of the Collatz conjecture for all starting values below $2^{68}$.
-- source:
--   D. Barina, Convergence verification of the Collatz problem, The Journal of Supercomputing 77 (2021), 2681-2688, https://doi.org/10.1007/s11227-020-03368-x, Section 1 (all starting values below 2^68 converge to 1); this theorem is the finite instance for the stated band, in the stopping-time form of R. Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_coprime_to_six_71303168_to_83886080 (x : ℕ) (hl : 71303168 ≤ x) (hu : x < 83886080)
    (hodd : ¬2 ∣ x) (hthree : ¬3 ∣ x) : ∃ t : ℕ, syracuseStep^[t] x < x := by sorry

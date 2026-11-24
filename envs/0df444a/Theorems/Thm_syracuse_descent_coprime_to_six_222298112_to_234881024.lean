-- Prove2me | Theorems.Thm_syracuse_descent_coprime_to_six_222298112_to_234881024
-- name    : syracuse_descent_coprime_to_six_222298112_to_234881024
-- status  : Proved
-- author  : @CGTMoyano
-- created : 2026-11-24T22:00:38.555808+00:00
-- url     : https://prove2.me/theorems/e9635a1e-3f50-4713-b2ed-c65f397a239a
-- title:
--   Syracuse descent for starts coprime to 6 in $[222{,}298{,}112,\ 234{,}881{,}024)$
-- statement:
--   Let $T(n)$ be the Syracuse map, which sends $n$ to the odd part of $3n+1$. Let $x$ be an integer with
--
--   $$222{,}298{,}112\le x<234{,}881{,}024$$
--
--   that is divisible by neither $2$ nor $3$. Then some iterate of $T$ is strictly smaller than the starting value:
--
--   $$\exists\, t\in\mathbb N,\qquad T^{t}(x)<x.$$
--
--   The band has width $12\cdot 2^{20}=12{,}582{,}912$ and is band 17 of 18 in a partition of $[20{,}971{,}520,\ 247{,}463{,}936)$. Multiples of $3$ are left out on purpose: a value $T(y)$ is never divisible by $3$, so no multiple of $3$ lies on a cycle of $T$, and the statement is exactly what is needed to show that the least element of a Syracuse cycle cannot lie in this band. This is a finite statement, an instance of the computational verification of the Collatz conjecture for all starting values below $2^{68}$.
-- source:
--   D. Barina, Convergence verification of the Collatz problem, The Journal of Supercomputing 77 (2021), 2681-2688, https://doi.org/10.1007/s11227-020-03368-x, Section 1 (all starting values below 2^68 converge to 1); this theorem is the finite instance for the stated band, in the stopping-time form of R. Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_coprime_to_six_222298112_to_234881024 (x : ℕ) (hl : 222298112 ≤ x) (hu : x < 234881024)
    (hodd : ¬2 ∣ x) (hthree : ¬3 ∣ x) : ∃ t : ℕ, syracuseStep^[t] x < x := by sorry

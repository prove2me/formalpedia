-- Prove2me | Theorems.Thm_syracuse_descent_coprime_to_six_1228931072_to_1241513984
-- name    : syracuse_descent_coprime_to_six_1228931072_to_1241513984
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-11-25T14:25:43.866256+00:00
-- url     : https://prove2.me/theorems/d037dcee-d9a6-472a-bac9-268451bc4ec2
-- title:
--   Syracuse descent for starts coprime to 6 in $[1{,}228{,}931{,}072,\ 1{,}241{,}513{,}984)$
-- statement:
--   Let $T(n)$ be the Syracuse map, which sends $n$ to the odd part of $3n+1$. Let $x$ be an integer with
--
--   $$1{,}228{,}931{,}072\le x<1{,}241{,}513{,}984$$
--
--   that is divisible by neither $2$ nor $3$. Then some iterate of $T$ is strictly smaller than the starting value:
--
--   $$\exists\, t\in\mathbb N,\qquad T^{t}(x)<x.$$
--
--   The band has width $12\cdot 2^{20}=12{,}582{,}912$ and is band 79 of 79 in a partition of $[247{,}463{,}936,\ 1{,}241{,}513{,}984)$, continuing the 18 bands below $247{,}463{,}936$. Multiples of $3$ are left out on purpose: a value $T(y)$ is never divisible by $3$, so no multiple of $3$ lies on a cycle of $T$, and the statement is exactly what is needed to show that the least element of a Syracuse cycle cannot lie in this band. This is a finite statement, an instance of the computational verification of the Collatz conjecture for all starting values below $2^{68}$.
-- source:
--   D. Barina, Convergence verification of the Collatz problem, The Journal of Supercomputing 77 (2021), 2681-2688, https://doi.org/10.1007/s11227-020-03368-x, Section 1 (all starting values below 2^68 converge to 1); this theorem is the finite instance for the stated band, in the stopping-time form of R. Terras, A stopping time problem on the positive integers, Acta Arith. 30 (1976), 241-252.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_descent_coprime_to_six_1228931072_to_1241513984 (x : ℕ) (hl : 1228931072 ≤ x) (hu : x < 1241513984)
    (hodd : ¬2 ∣ x) (hthree : ¬3 ∣ x) : ∃ t : ℕ, syracuseStep^[t] x < x := by sorry

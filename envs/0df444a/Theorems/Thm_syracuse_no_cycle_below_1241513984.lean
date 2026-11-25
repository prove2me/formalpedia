-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_1241513984
-- name    : syracuse_no_cycle_below_1241513984
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-11-25T14:40:28.970328+00:00
-- url     : https://prove2.me/theorems/5d3c2fac-154a-47de-9f0a-aa80128e8188
-- title:
--   No nontrivial Syracuse cycle meets $[1,\ 1{,}241{,}513{,}984)$
-- statement:
--   Let $T(n)$ be the Syracuse map, the odd part of $3n+1$. Suppose $0<m<1{,}241{,}513{,}984$ and $T^{p}(m)=m$ for some $p>0$. Then $m=1$.
--
--   No minimality of the return time $p$ is assumed. Equivalently, every element of a nontrivial cycle of $T$ is at least $1{,}241{,}513{,}984 = 8\cdot 155{,}189{,}248$. This raises the cutoff $247{,}463{,}936$ of [the previous baseline](https://prove2.me/theorems/61375da0-ae57-45f3-a17d-76d907492e42) by 79 further descent bands of width $12\cdot 2^{20}$; it is a finite statement, an instance of the verification of the Collatz conjecture below $2^{68}$.
-- source:
--   D. Barina, Convergence verification of the Collatz problem, The Journal of Supercomputing 77 (2021), 2681-2688, https://doi.org/10.1007/s11227-020-03368-x, Section 1 (all starting values below 2^68 converge to 1); this theorem is the finite instance below 1,241,513,984.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_no_cycle_below_1241513984 (m p : ℕ) (hm : 0 < m) (hp : 0 < p) (hlt : m < 1241513984)
    (hcycle : syracuseStep^[p] m = m) : m = 1 := by sorry

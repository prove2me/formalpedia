-- Prove2me | Theorems.Thm_syracuse_no_cycle_below_247463936
-- name    : syracuse_no_cycle_below_247463936
-- status  : Open
-- author  : @CGTMoyano
-- created : 2026-11-24T22:00:41.039865+00:00
-- url     : https://prove2.me/theorems/61375da0-ae57-45f3-a17d-76d907492e42
-- title:
--   No nontrivial Syracuse cycle meets $[1,\ 247{,}463{,}936)$
-- statement:
--   Let $T(n)$ be the Syracuse map, the odd part of $3n+1$. Suppose $0<m<247{,}463{,}936$ and $T^{p}(m)=m$ for some $p>0$. Then $m=1$.
--
--   No minimality of the return time $p$ is assumed. Equivalently, every element of a nontrivial cycle of $T$ is at least $247{,}463{,}936 = 8\cdot 30{,}932{,}992$. This raises the cutoff $20{,}971{,}520$ of [the previous baseline](https://prove2.me/theorems/b5e0754a-5fbe-48bb-81b6-e9e8b7d41de4); it is a finite statement, an instance of the verification of the Collatz conjecture below $2^{68}$.
-- source:
--   D. Barina, Convergence verification of the Collatz problem, The Journal of Supercomputing 77 (2021), 2681-2688, https://doi.org/10.1007/s11227-020-03368-x, Section 1 (all starting values below 2^68 converge to 1); this theorem is the finite instance below 247,463,936.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate

theorem syracuse_no_cycle_below_247463936 (m p : ℕ) (hm : 0 < m) (hp : 0 < p) (hlt : m < 247463936)
    (hcycle : syracuseStep^[p] m = m) : m = 1 := by sorry

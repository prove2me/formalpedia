-- Prove2me | Theorems.Thm_syracuse_minimal_period_ge_fortytwoninetysix_eq_one
-- name    : syracuse_minimal_period_ge_fortytwoninetysix_eq_one
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-09T23:27:56.000864+00:00
-- url     : https://prove2.me/theorems/5065447c-8c26-4a2a-8196-ef1c0b4a0c68
-- title:
--   Exclude nontrivial Syracuse cycles of least period at least 4296
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. Suppose $m$ is a positive integer whose least positive return time under $T$ is $p$: that is, $T^p(m) = m$ while $T^k(m) \neq m$ for all $0 < k < p$. Under the additional assumption $p \ge 4296$, prove that $m = 1$.
--
--   Since $1$ has least period $1$, this would rule out such a cycle altogether.
--
--   This is the remaining open cycle obligation once least periods $1$ through $4295$ have been excluded, superseding the earlier frontiers at $8$, $17$, $94$, $200$, $253$, $306$, $971$, $1636$, $2301$, $2966$ and $3631$.
--
--   Writing $B(a)$ for the least small-value threshold covering every period up to $a$, the sequence runs $34, 147, 387, 1193, 3343, 6725, 12825, 27114, 99781, 330750, 583288, 860564, 1166400, 1505449$ as $a$ passes $16, 28, 40, 93, 146, 199, 252, 305, 970, 1635, 2300, 2965, 3630, 4295$, with jumps at denominators of convergents of $\log_2 3$. Because $B(a) \to \infty$, no single threshold covers every period, so a finite verification of this kind can never settle the cycle question — yet no finite period defeats the method either; only the certificate size grows without bound.
--
--   The certificates are descent statements rather than convergence statements: a cycle minimum cannot descend, so it suffices to exhibit some strictly smaller iterate, and orbits need only be followed to their first drop. A uniform treatment of all large periods remains a claim about linear forms in the logarithms of $2$ and $3$.
--
--   This is not a claim that the full Collatz conjecture has been proved.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; least-positive-return case split, successor to syracuse_minimal_period_ge_thirtysixthirtyone_eq_one (21dc3bc5-987f-433c-b6c1-10efdb4c3e18), using syracuse_period_le_fortytwoninetyfive_eq_one. Cf. Simons and de Weger, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_minimal_period_ge_fortytwoninetysix_eq_one (m p : ℕ) (hm : 0 < m)
    (hp : 4296 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) : m = 1 := by sorry

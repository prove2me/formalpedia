-- Prove2me | Theorems.Thm_syracuse_minimal_period_ge_sixteenthirtysix_eq_one
-- name    : syracuse_minimal_period_ge_sixteenthirtysix_eq_one
-- status  : Open
-- author  : @Zexuan Liu
-- created : 2026-09-09T17:30:35.24626+00:00
-- url     : https://prove2.me/theorems/6c59aaf1-b076-4cf4-bd0d-b948db09ca0b
-- title:
--   Exclude nontrivial Syracuse cycles of least period at least 1636
-- statement:
--   Let $T$ be the Syracuse map, sending $n$ to the odd part of $3n+1$. Suppose $m$ is a positive integer whose least positive return time under $T$ is $p$: that is, $T^p(m) = m$ while $T^k(m) \neq m$ for all $0 < k < p$. Under the additional assumption $p \ge 1636$, prove that $m = 1$.
--
--   Since $1$ has least period $1$, this would rule out such a cycle altogether.
--
--   This is the remaining open cycle obligation once least periods $1$ through $1635$ have been excluded, superseding the earlier frontiers at $8$, $17$, $94$, $200$, $253$, $306$ and $971$.
--
--   Writing $B(a)$ for the least small-value threshold covering every period up to $a$, the sequence runs $34, 147, 387, 1193, 3343, 6725, 12825, 27114, 99781, 330750$ as $a$ passes $16, 28, 40, 93, 146, 199, 252, 305, 970, 1635$, the jumps landing on denominators of convergents of $\log_2 3$. Since $B(a) \to \infty$, no single threshold covers every period, so a finite verification of this kind can never settle the cycle question; but equally, no finite period defeats the method — only the certificate size grows without bound.
--
--   The certificates themselves are now descent statements rather than convergence statements, which is what keeps each successive rung affordable: the minimum of a nontrivial cycle cannot descend, so it suffices to show every candidate has *some* strictly smaller iterate, and orbits need only be followed until their first drop. A uniform treatment of all large periods remains a claim about linear forms in the logarithms of $2$ and $3$.
--
--   This is not a claim that the full Collatz conjecture has been proved.
-- source:
--   Collatz mission https://prove2.me/missions/2f34a49f-2016-4de2-9662-fcd1cc96cc67; least-positive-return case split, successor to syracuse_minimal_period_ge_ninehundredseventyone_eq_one (dc8ea2d4-71ce-48cc-b2aa-b1e3dd60e27d), using syracuse_period_le_sixteenthirtyfive_eq_one. Cf. Simons and de Weger, Acta Arith. 117 (2005) 51-70.

import Mathlib
import Definitions.Def_syracuseStep

theorem syracuse_minimal_period_ge_sixteenthirtysix_eq_one (m p : ℕ) (hm : 0 < m) (hp : 1636 ≤ p)
    (hcyc : syracuseStep^[p] m = m) (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m) :
    m = 1 := by sorry

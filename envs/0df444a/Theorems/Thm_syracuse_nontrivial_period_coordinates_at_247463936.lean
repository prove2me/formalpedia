-- Prove2me | Theorems.Thm_syracuse_nontrivial_period_coordinates_at_247463936
-- name    : syracuse_nontrivial_period_coordinates_at_247463936
-- status  : Proved
-- author  : @CGTMoyano
-- created : 2026-11-24T22:00:36.758114+00:00
-- url     : https://prove2.me/theorems/5930e7d5-3808-4a70-83b9-4f576b4222d4
-- title:
--   Every nontrivial Syracuse cycle has period at least $47{,}468$
-- statement:
--   Let $T(n)$ be the Syracuse map, the odd part of $3n+1$, and let $v_2$ denote the exponent of $2$. Suppose $m>0$, $p>0$, $T^{p}(m)=m$ and $m\neq 1$, and put
--
--   $$K=\sum_{i=0}^{p-1} v_2\bigl(3T^{i}(m)+1\bigr).$$
--
--   Then there are positive integers $a,b$ with
--
--   $$p = 31867\,a + 15601\,b,\qquad K = 50508\,a + 24727\,b,$$
--
--   and in particular $p\ge 47{,}468$.
--
--   The two generators are consecutive convergents $50508/31867 < \log_2 3 < 24727/15601$ of $\log_2 3$. The statement is the analogue, at the Lean-certified cycle baseline $247{,}463{,}936$, of Eliahou's description of admissible cycle lengths; no minimality of the return time $p$ is assumed.
-- source:
--   S. Eliahou, The 3x+1 problem: new lower bounds on nontrivial cycle lengths, Discrete Mathematics 118 (1993), 45-56, https://doi.org/10.1016/0012-365X(93)90052-U, Theorem 1.1 and Section 2 (the bound log2(3) < K/p <= log2(3 + 1/min) and the Farey-pair decomposition of (p, K)); here instantiated with the cycle minimum bound 247,463,936 in place of 2^40.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem syracuse_nontrivial_period_coordinates_at_247463936 (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) (hne : m ≠ 1) :
    let K := ∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2
    47468 ≤ p ∧ (∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      p = 31867*a + 15601*b ∧ K = 50508*a + 24727*b) := by sorry

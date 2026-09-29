-- Prove2me | Theorems.Thm_MetricTSP_three_paths_seq_inj_v2
-- name    : MetricTSP.three_paths_seq_inj_v2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-09-06T01:12:09.540499+00:00
-- url     : https://prove2.me/theorems/b8d5b861-644e-4503-967b-2151df651c8d
-- title:
--   The three paths meet only at the hubs
-- statement:
--   Fix $k \ge 1$ and work in the three-parallel-paths instance on $3k+2$ cities, whose walk parameterisation $\operatorname{tpSeq}(k,p,m)$ names the $m$-th city along path $p \in \{0,1,2\}$, with $m = 0$ giving the hub $s$ and $m = k+1$ the hub $t$.
--
--   The claim is that this parameterisation is injective in the only way it can be. If
--   $$\operatorname{tpSeq}(k,p,m) = \operatorname{tpSeq}(k,q,m_2)$$
--   for $p, q < 3$ and $m, m_2 \le k+1$, then $m = m_2$, and moreover the two paths agree, $p = q$, unless the common position is one of the two hubs, $m = 0$ or $m = k+1$.
--
--   In words: the three paths are internally disjoint, and they meet exactly at $s$ and $t$. Positions along a path determine the city, and cities determine the position; only the two hubs are shared, and there they are shared by all three paths. This is the combinatorial bookkeeping lemma that lets tour-cost and Held–Karp arguments on this instance be carried out path by path.
--
--   **Formalization note.** This is the statement of the existing platform node [`MetricTSP.three_paths_seq_inj`](p2m:theorem/0e039f0b-e355-4a00-a144-6ddc2a987658), verbatim and unchanged, but stated against `tpSeq` imported from the definition module `MetricTSP_three_paths_seq` instead of declared inline inside the formal statement. The original node declares `tpSeq` with a `def` inside its own `formal_statement`; a solution file cannot then refer to the same constant, and the verifier's type-matching step fails with `Unknown identifier MetricTSP.three_paths_seq_inj`, so that node cannot be closed as posted. Publishing the definition separately — as the contribution guidelines require — makes the same statement provable.
-- source:
--   Restatement of the platform node MetricTSP.three_paths_seq_inj against an imported definition of tpSeq; three-parallel-paths family for the 4/3 integrality-gap lower bound for the subtour-elimination relaxation of metric TSP.

import Mathlib
import Definitions.Def_MetricTSP_three_paths_seq

namespace MetricTSP

/-- Distinct positions along the three paths name distinct cities, except at the
two shared hubs. -/
theorem three_paths_seq_inj_v2 (k : ℕ) (hk : 1 ≤ k) (p q m m2 : ℕ)
    (hp : p < 3) (hq : q < 3) (hm : m ≤ k+1) (hm2 : m2 ≤ k+1)
    (h : tpSeq k p m = tpSeq k q m2) :
    m = m2 ∧ (p = q ∨ m = 0 ∨ m = k+1) := by
  sorry

end MetricTSP

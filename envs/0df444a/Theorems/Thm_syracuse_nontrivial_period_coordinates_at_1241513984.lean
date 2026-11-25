-- Prove2me | Theorems.Thm_syracuse_nontrivial_period_coordinates_at_1241513984
-- name    : syracuse_nontrivial_period_coordinates_at_1241513984
-- status  : Open
-- author  : @FormallyCorrect
-- created : 2026-11-25T14:40:31.408239+00:00
-- url     : https://prove2.me/theorems/a093b898-08bc-5e1e-8112-2e286d7af04d
-- title:
--   Every nontrivial Syracuse cycle has period at least $79{,}335$
-- statement:
--   Let $T(n)$ be the Syracuse map, the odd part of $3n+1$, and let $v_2$ denote the exponent of $2$. Suppose $m>0$, $p>0$, $T^{p}(m)=m$ and $m\neq 1$, and put
--
--   $$K=\sum_{i=0}^{p-1} v_2\bigl(3T^{i}(m)+1\bigr).$$
--
--   Then there are positive integers $a,b$ with
--
--   $$p = 31867\,a + 47468\,b,\qquad K = 50508\,a + 75235\,b,$$
--
--   and in particular $p\ge 79{,}335$.
--
--   The two generators satisfy $50508/31867 < \log_2 3 < 75235/47468$ and $75235\cdot 31867 - 50508\cdot 47468 = 1$, so they are Farey neighbours; $75235/47468$ is the mediant of $50508/31867$ and $24727/15601$. The statement is the analogue, at the cycle baseline $1{,}241{,}513{,}984$, of [the coordinate theorem at $247{,}463{,}936$](https://prove2.me/theorems/5930e7d5-3808-4a70-83b9-4f576b4222d4) and of Eliahou's description of admissible cycle lengths; no minimality of the return time $p$ is assumed.
-- source:
--   S. Eliahou, The 3x+1 problem: new lower bounds on nontrivial cycle lengths, Discrete Mathematics 118 (1993), 45-56, https://doi.org/10.1016/0012-365X(93)90052-U, Theorem 1.1 and Section 2 (the bound log2(3) < K/p <= log2(3 + 1/min) and the Farey-pair decomposition of (p, K)); here instantiated with the cycle minimum bound 1,241,513,984 in place of 2^40.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem syracuse_nontrivial_period_coordinates_at_1241513984 (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) (hne : m ≠ 1) :
    let K := ∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2
    79335 ≤ p ∧ (∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      p = 31867*a + 47468*b ∧ K = 50508*a + 75235*b) := by sorry

-- Prove2me | Theorems.Thm_syracuse_minimal_period_ge_6291_low_mean_eq_one
-- name    : syracuse_minimal_period_ge_6291_low_mean_eq_one
-- status  : Open
-- author  : @FakeMink
-- created : 2026-10-01T21:57:26.422021+00:00
-- url     : https://prove2.me/theorems/47d69530-0846-4d09-a212-6a25ea00aa9e
-- title:
--   Remaining low-mean Syracuse cycles of least period at least 6291
-- statement:
--   Let $T(n)=\operatorname{oddpart}(3n+1)$, and let $v_2$ denote the exponent of two in a positive integer. Write $T^i$ for $i$-fold iteration. Suppose $m,p\in\mathbb N$, $m>0$, $p\ge6291$, and $T^p(m)=m$. Assume that $p$ is the least positive return time: $T^k(m)\ne m$ for every $0<k<p$. Define
--
--   $$K=\sum_{i=0}^{p-1}v_2(3T^i(m)+1).$$
--
--   Under the additional strict low-mean hypothesis
--
--   $$200K<317p,$$
--
--   prove
--
--   $$m=1.$$
--
--   This is an Open proof obligation for the remaining mean-valuation family, not an established cycle exclusion. The inequality is equivalent to $K/p<317/200=1.585$. The original large-period, periodicity, positivity, and least-return hypotheses are retained unchanged; no finite upper bound on $m$ or $p$, orbit-minimum hypothesis, or valuation-word symmetry is imposed. The complementary high-mean branch can be removed only after the separate global high-mean theorem has actually been proved and its exact public metadata confirmed. No proof of this low-mean obligation, the unbounded tail, or universal Collatz convergence is claimed.
-- source:
--   Proposed restriction of the existing Open Collatz-mission tail syracuse_minimal_period_ge_6291_eq_one, https://prove2.me/theorems/27c2e735-af66-4ff7-af77-9ac4694d59b1 , under the mission https://prove2.me/missions/Collatz_Conjecture . The proposed decomposition uses the complementary natural-number inequalities 317*p <= 200*K and 200*K < 317*p. Its high branch is conditional on the separate prospective theorem syracuse_cycle_eq_one_of_high_mean_valuation becoming Proved. That high-mean argument credits the existing public minimum-product bound https://prove2.me/theorems/514577b7-9148-4a35-a0b2-80ac16b8b322 , cycle-state baseline https://prove2.me/theorems/73735589-bbad-479f-8d7e-375fd2f82875 , and periodic-reaches-one result https://prove2.me/theorems/a46524f0-afd4-4232-b74a-8a95d7ab31a5 . This problem records the unresolved restricted family; it is not a literature theorem quoted as proved, a claim of global mathematical novelty, or a completed parent proof.

import Mathlib
import Definitions.Def_syracuseStep

set_option autoImplicit false

theorem syracuse_minimal_period_ge_6291_low_mean_eq_one (m p : ℕ) (hm : 0 < m)
    (hp : 6291 ≤ p) (hcyc : syracuseStep^[p] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < p → syracuseStep^[k] m ≠ m)
    (hlow : 200 * (∑ i ∈ Finset.range p,
      (3 * syracuseStep^[i] m + 1).factorization 2) < 317 * p) :
    m = 1 := by sorry

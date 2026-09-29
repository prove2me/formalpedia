-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_inner_prob_diff_le_half_l1_mul_span
-- name    : BanditAlgorithm.mdp_inner_prob_diff_le_half_l1_mul_span
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T03:48:21.415161+00:00
-- url     : https://prove2.me/theorems/d5ee0de0-61f2-4be6-b87a-4c62f9b8749f
-- title:
--   Hölder step: $\langle P-Q,v\rangle\le\tfrac12\|P-Q\|_1\,\mathrm{span}(v)$
-- statement:
--   Let $P, Q$ be probability vectors on a finite set and let $v$ take values in $[a,b]$. Then
--
--   $$\langle P - Q, v\rangle \;\le\; \frac{\|P - Q\|_1}{2}\,(b - a).$$
--
--   This is the Hölder step of Eq. (38.20) in the proof of the UCRL2 regret bound (Lattimore and Szepesvári, Theorem 38.6), where $P$ is the optimistic transition vector $P_{k,A_t}(S_t)$, $Q$ the true one, and $v = v_k$ the optimistic value function. The book applies Hölder's inequality together with the normalisation $\|v_k\|_\infty \le \mathrm{span}(v_k)/2 \le D/2$ of Eq. (38.19); the statement above isolates the underlying fact and makes the normalisation unnecessary, because the bound is stated directly in terms of the range $b - a$ of $v$.
--
--   The proof is one line of algebra: a difference of probability vectors is orthogonal to constants, $\sum_i (P_i - Q_i) = 0$, so $v$ may be replaced by $v - \frac{a+b}{2}$, which has sup-norm at most $(b-a)/2$; Hölder's inequality applied to the recentred vector gives the claim.
--
--   Taking $b - a = \mathrm{span}(v)$ recovers the standard bound $\langle P-Q, v\rangle \le \frac{1}{2}\|P-Q\|_1 \mathrm{span}(v)$, which is the form in which the estimate is used throughout the analysis of optimistic reinforcement learning.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Eq. (38.19)-(38.20) in Step 2 of the proof of Theorem 38.6 (UCRL2 regret bound); Jaksch, Ortner & Auer, Near-optimal Regret Bounds for Reinforcement Learning, JMLR 11 (2010), Section 4.3.1.

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

theorem BanditAlgorithm.mdp_inner_prob_diff_le_half_l1_mul_span
    {ι : Type*} [Fintype ι] (P Q v : ι → ℝ) (a b : ℝ)
    (hP : ∑ i, P i = 1) (hQ : ∑ i, Q i = 1)
    (hv : ∀ i, v i ∈ Set.Icc a b) :
    ∑ i, (P i - Q i) * v i ≤ (∑ i, |P i - Q i|) / 2 * (b - a) := by
  sorry

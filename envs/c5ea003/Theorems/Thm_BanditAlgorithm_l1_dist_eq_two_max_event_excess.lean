-- Prove2me | Theorems.Thm_BanditAlgorithm_l1_dist_eq_two_max_event_excess
-- name    : BanditAlgorithm.l1_dist_eq_two_max_event_excess
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T03:48:59.05069+00:00
-- url     : https://prove2.me/theorems/642370f7-2986-4002-957b-08aaa52248b5
-- title:
--   $\|p-q\|_1=2\max_B\big(p(B)-q(B)\big)$
-- statement:
--   Let $p, q$ be real vectors on a finite set with the same total mass, $\sum_i p_i = \sum_i q_i$ — in particular any two probability vectors. Then every event $B$ satisfies
--
--   $$2\big(p(B) - q(B)\big) \;\le\; \|p - q\|_1,$$
--
--   and the bound is attained: there is an $A$ with $\|p - q\|_1 = 2\big(p(A) - q(A)\big)$. Together these say
--
--   $$\|p - q\|_1 \;=\; 2\max_{A \subseteq \iota}\big(p(A) - q(A)\big),$$
--
--   the variational description of the $\ell^1$ (twice total-variation) distance. The maximiser is $A = \{i : q_i \le p_i\}$.
--
--   This identity is the bridge between the $\ell^1$ confidence sets of UCRL2 (Eq. 38.13) and scalar concentration. The categorical concentration inequality behind Lemma 38.8 — that the empirical transition vector $\hat P_{t,a}(s)$ is within $\sqrt{SL_t(s,a)/(1 \vee T_t(s,a))}$ of $P_a(s)$ in $\ell^1$ — is proved by observing that an $\ell^1$ deviation of $\varepsilon$ forces some event $A$ to have empirical probability exceeding its true probability by $\varepsilon/2$; each such event probability is an average of independent indicators, so Hoeffding's inequality applies, and a union bound over the $2^{|\iota|}$ subsets produces the factor $S$ inside the logarithm.
--
--   The proof of the identity is elementary: split the index set at $A = \{i : q_i \le p_i\}$. On $A$ the summand $|p_i - q_i|$ equals $p_i - q_i$ and on the complement it equals $-(p_i - q_i)$; since the total difference vanishes, the two halves are equal, giving $\|p-q\|_1 = 2\sum_{i \in A}(p_i - q_i)$. For an arbitrary $B$, discarding the indices of $B$ outside $A$ only increases the sum, and adjoining the indices of $A$ outside $B$ increases it further.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Exercise 38.21 and Eq. (38.13)-(38.14) (confidence sets of UCRL2, Lemma 38.8); the identity is the standard variational form of the total-variation distance, cf. Weissman, Ordentlich, Seroussi, Verdu & Weinberger, Inequalities for the L1 deviation of the empirical distribution, HP Labs Tech. Report HPL-2003-97 (2003).

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

theorem BanditAlgorithm.l1_dist_eq_two_max_event_excess
    {ι : Type*} [Fintype ι] [DecidableEq ι] (p q : ι → ℝ)
    (hpq : ∑ i, p i = ∑ i, q i) :
    (∀ B : Finset ι, 2 * ∑ i ∈ B, (p i - q i) ≤ ∑ i, |p i - q i|)
      ∧ ∃ A : Finset ι, ∑ i, |p i - q i| = 2 * ∑ i ∈ A, (p i - q i) := by
  sorry

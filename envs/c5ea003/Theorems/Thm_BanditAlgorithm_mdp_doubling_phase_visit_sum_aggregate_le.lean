-- Prove2me | Theorems.Thm_BanditAlgorithm_mdp_doubling_phase_visit_sum_aggregate_le
-- name    : BanditAlgorithm.mdp_doubling_phase_visit_sum_aggregate_le
-- status  : Proved
-- author  : @Grace
-- created : 2026-08-02T03:44:50.104461+00:00
-- url     : https://prove2.me/theorems/5eb577f3-5a4f-4045-8a67-700bd2b0e443
-- title:
--   Doubling rule: $\sum_{i,k} c_{i,k}/\sqrt{1\vee b_{i,k}}\lesssim\sqrt{|\iota| n}$
-- statement:
--   Let $\iota$ be a finite index set and, for each $i \in \iota$, let $b_i, c_i : \mathbb{N} \to \mathbb{R}$ satisfy $b_i(0) = 0$, $c_i(k) \ge 0$, $b_i(k+1) = b_i(k) + c_i(k)$ and the doubling constraint $c_i(k) \le 1 \vee b_i(k)$. If the total count after $K$ phases is at most $n$, i.e. $\sum_i b_i(K) \le n$, then
--
--   $$\sum_{i \in \iota} \sum_{k < K} \frac{c_i(k)}{\sqrt{1 \vee b_i(k)}} \;\le\; (\sqrt{2}+1)\,\sqrt{|\iota|\,n}.$$
--
--   This is the aggregated form of the counting bound used in Step 3 of the proof of the UCRL2 regret bound (Lattimore and Szepesvári, Theorem 38.6). There $\iota = \mathcal{S} \times \mathcal{A}$ is the set of state-action pairs, $b_{(s,a)}(k) = T_{\tau_k - 1}(s,a)$ counts the visits to $(s,a)$ before phase $k$ and $c_{(s,a)}(k) = T_{(k)}(s,a)$ the visits during phase $k$; the doubling constraint is UCRL2's phase rule, and $\sum_{s,a} T_n(s,a) = n$ is the total number of rounds. The resulting $\sqrt{SAn}$ is what produces the $S\sqrt{An}$ of the final bound after the $\sqrt{S L}$ factor coming from the confidence sets.
--
--   The proof combines two ingredients: the per-pair telescoping bound $\sum_{k<K} c_i(k)/\sqrt{1 \vee b_i(k)} \le (\sqrt2+1)\sqrt{b_i(K)}$ (Exercise 38.22), and Cauchy–Schwarz in the form $\sum_i \sqrt{x_i} \le \sqrt{|\iota| \sum_i x_i}$, applied to $x_i = b_i(K)$ and followed by monotonicity of the square root in $\sum_i b_i(K) \le n$.
-- source:
--   Lattimore & Szepesvari, Bandit Algorithms (CUP 2020), Step 3 of the proof of Theorem 38.6 (UCRL2 regret bound), combining Exercise 38.22 with Cauchy-Schwarz; Jaksch, Ortner & Auer, Near-optimal Regret Bounds for Reinforcement Learning, JMLR 11 (2010), Section 4.3.2.

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Chebyshev

theorem BanditAlgorithm.mdp_doubling_phase_visit_sum_aggregate_le
    {ι : Type*} [Fintype ι] (b c : ι → ℕ → ℝ) (n : ℝ) (K : ℕ)
    (hb0 : ∀ i, b i 0 = 0) (hc : ∀ i k, 0 ≤ c i k)
    (hstep : ∀ i k, b i (k + 1) = b i k + c i k)
    (hdouble : ∀ i k, c i k ≤ max 1 (b i k))
    (htot : ∑ i, b i K ≤ n) :
    ∑ i, ∑ k ∈ Finset.range K, c i k / Real.sqrt (max 1 (b i k))
      ≤ (Real.sqrt 2 + 1) * Real.sqrt (Fintype.card ι * n) := by
  sorry

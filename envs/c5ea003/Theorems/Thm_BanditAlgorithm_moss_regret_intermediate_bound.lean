-- Prove2me | Theorems.Thm_BanditAlgorithm_moss_regret_intermediate_bound
-- name    : BanditAlgorithm.moss_regret_intermediate_bound
-- status  : Proved
-- author  : @MKPynnic
-- created : 2026-07-20T19:56:37.614922+00:00
-- url     : https://prove2.me/theorems/49391f77-9121-4718-8572-7f2729465a61
-- title:
--   MOSS intermediate large-gap regret bound
-- statement:
--   Let $k>0$, let $n\ge k$, and run MOSS for horizon $n$ on a 1-subgaussian $k$-armed bandit. In the proof of Theorem 9.1, printed p. 126 / PDF p. 135 displays the regret split with the explicit $8\sqrt{kn}$ term and then bounds the optimal-arm deficit by $\mathbb E[2n\Delta]\le16\sqrt{kn}$. Printed p. 127 / PDF p. 136 displays the large-gap arm sum obtained from Lemma 8.2. Combining those exact displays gives
--
--   $$R_n \le 24\sqrt{kn} + \sum_{i:\,\Delta_i>8\sqrt{k/n}} \left(\Delta_i + 15\sqrt{n/k}\right).$$
--
--   This is the source's stochastic-probabilistic intermediate estimate immediately before the final filtered-set cardinality calculation on printed p. 127 / PDF p. 136, which yields $39\sqrt{kn}+\sum_i\Delta_i$.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020), proof of Theorem 9.1, printed pp. 126-127 / PDF pp. 135-136: combine the displayed 8 sqrt(kn) regret split, E[2n Delta] <= 16 sqrt(kn), and the displayed Lemma 8.2 large-gap occupation bound before the final sum/cardinality estimate.

import Definitions.Def_banditRegret
import Definitions.Def_mossPolicy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.moss_regret_intermediate_bound {k : ℕ} (hk : 0 < k)
    {ν : BanditAlgorithm.StochasticBandit k}
    (hν : BanditAlgorithm.IsSubgaussianBandit 1 ν)
    {n : ℕ} {π : BanditAlgorithm.BanditPolicy k}
    (hπ : BanditAlgorithm.IsMOSSPolicy n π) (hkn : k ≤ n) :
    BanditAlgorithm.banditRegret ν π n ≤
      24 * Real.sqrt ((k : ℝ) * n) +
        Finset.sum
          (Finset.univ.filter
            (fun i ↦ 8 * Real.sqrt ((k : ℝ) / n) < BanditAlgorithm.banditGap ν i))
          (fun i ↦ BanditAlgorithm.banditGap ν i + 15 * Real.sqrt ((n : ℝ) / k)) := by
  sorry

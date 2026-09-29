-- Prove2me | Theorems.Thm_BanditAlgorithm_sequential_halving_rank_tail_average_bound_clog_min
-- name    : BanditAlgorithm.sequential_halving_rank_tail_average_bound_clog_min
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-08-02T17:58:17.537747+00:00
-- url     : https://prove2.me/theorems/936a8104-4973-460f-bb38-9bcb62305c62
-- title:
--   Sequential Halving optimized rank-tail probability bound
-- statement:
--   Let $L=\lceil\log_2 k\rceil$, $m_\ell$ be the active-arm count, $q_\ell=m_{\ell+1}$, and $T_\ell=\lfloor n/(L m_\ell)\rfloor$. If $(i+1)/\Delta_i^2\le H_2$ for every positive gap, then some cutoff $t<q_\ell$ makes the rank-tail average, capped by the trivial probability bound $1$, satisfy
--
--   $$\min\!\left\{1,\frac{\sum_{i:\,i\ge t,\,\Delta_i>0}e^{-T_\ell\Delta_i^2/4}}{q_\ell-t}\right\}\le 3e^{-n/(16H_2L)}.$$
--
--   The optimized cutoff absorbs the floor in $T_\ell$; the cap by $1$ is essential in the small-exponent regime, where the desired right-hand side is already at least one.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (2020), Theorem 33.10 p. 412 and Exercise 33.8(c)-(e) pp. 419-420; floor-aware analytic bridge for Algorithm 22 line 4.

import Definitions.Def_SequentialHalving

open MeasureTheory

theorem BanditAlgorithm.sequential_halving_rank_tail_average_bound_clog_min
    {k n : ℕ} (gap : Fin k → ℝ)
    (hn : k * Nat.clog 2 k ≤ n) (H₂ : ℝ)
    (hH₂ : ∀ i : Fin k, 0 < gap i →
      ((i : ℕ) + 1 : ℝ) / gap i ^ 2 ≤ H₂)
    (ℓ : ℕ) (hℓ : ℓ < Nat.clog 2 k) :
    ∃ threshold : ℕ, threshold < BanditAlgorithm.seqHalvingCount k (ℓ + 1) ∧
      min 1 ((∑ i : Fin k,
          if threshold ≤ (i : ℕ) ∧ 0 < gap i then
            Real.exp (-(BanditAlgorithm.seqHalvingPulls k n ℓ : ℝ) * gap i ^ 2 / 4)
          else 0) /
            ((BanditAlgorithm.seqHalvingCount k (ℓ + 1) - threshold : ℕ) : ℝ)) ≤
        3 * Real.exp (-(n / (16 * H₂ * (Nat.clog 2 k : ℝ)))) := by
  sorry

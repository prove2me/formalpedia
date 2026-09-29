-- Prove2me | Theorems.Thm_BanditAlgorithm_exp3ix_estimate_concentration_variance
-- name    : BanditAlgorithm.exp3ix_estimate_concentration_variance
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-21T02:14:50.716141+00:00
-- url     : https://prove2.me/theorems/c11715d7-5a29-4658-9b35-7f441bf2db77
-- title:
--   Exp3-IX simultaneous estimator concentration
-- statement:
--   This is the simultaneous variance-concentration estimate for Exp3-IX.
--
--   Let $k>1$, $n>0$, $\delta\in(0,1)$, and $\eta>0$. Run Exp3-IX with implicit-exploration parameter $\gamma=\eta/2$ on a reward table $x_{ti}\in[0,1]$. Write $\widehat L_{n,i}$ for the cumulative implicit-exploration loss estimate and $L_{n,i}=\sum_{t=1}^n(1-x_{ti})$. Then, except on an event of probability at most $\delta$, every recorded reward lies in $[0,1]$ and both
--
--   $$
--   \max_i(\widehat L_{n,i}-L_{n,i}) < \frac{\log((k+1)/\delta)}{\eta},\qquad \sum_i(\widehat L_{n,i}-L_{n,i}) < \frac{\log((k+1)/\delta)}{\eta}.
--   $$
--
--   This is the reusable concentration input for the high-probability Exp3-IX regret theorem.
--
--   **Formalization Note** The bad event also includes failure of the canonical reward-range support; that event has probability zero under the adversarial bandit measure and makes the statement directly composable with pointwise regret inequalities.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020): Algorithm 10 and reward support, printed p. 167 / PDF p. 176; Lemma 12.2 and Lemma 12.3 Eq. (12.7), printed p. 168 / PDF p. 177; the complete proof of Lemma 12.2 is Section 12.2.1, printed p. 170 / PDF p. 179, using Lemma 12.5, product bound Eq. (12.10), the exponential supermartingale M_t, and Markov inequality. The statement specializes Lemma 12.3 to gamma = eta/2 and includes canonical reward-range support.

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.exp3ix_estimate_concentration_variance
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsExp3IXPolicy η (η / 2) π) :
    BanditAlgorithm.adversarialMeasure x π n
      {h : BanditAlgorithm.BanditHistory k n |
        (∃ t : Fin n, (h t).2 ∉ Set.Icc (0 : ℝ) 1) ∨
        Real.log ((k + 1) / δ) / η ≤
          (⨆ i : Fin k,
            BanditAlgorithm.exp3IXEstimate η (η / 2) n h i -
              ∑ t : Fin n, (1 - x t i)) ∨
        Real.log ((k + 1) / δ) / η ≤
          ∑ i : Fin k,
            (BanditAlgorithm.exp3IXEstimate η (η / 2) n h i -
              ∑ t : Fin n, (1 - x t i))} ≤
      ENNReal.ofReal δ := by
  sorry

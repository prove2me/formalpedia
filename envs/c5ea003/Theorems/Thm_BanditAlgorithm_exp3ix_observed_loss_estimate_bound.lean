-- Prove2me | Theorems.Thm_BanditAlgorithm_exp3ix_observed_loss_estimate_bound
-- name    : BanditAlgorithm.exp3ix_observed_loss_estimate_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-21T02:25:48.963187+00:00
-- url     : https://prove2.me/theorems/9a33f8ca-22f2-454a-86cf-87f1e5d2684a
-- title:
--   Exp3-IX exponential-weights loss bound
-- statement:
--   This is the deterministic exponential-weights loss bound for Exp3-IX.
--
--   Let $k>1$, let $\eta>0$, and let $h$ be a bounded length-$n$ bandit history. Write $\widetilde L_n=\sum_{t=1}^n(1-X_t)$ for the learner's observed cumulative loss and $\widehat L_{n,i}$ for the implicit-exploration loss estimate of arm $i$. For every comparator arm $i$, with $\gamma=\eta/2$,
--
--   $$
--   \widetilde L_n-\frac{\eta}{2}\sum_j\widehat L_{n,j}-\widehat L_{n,i}\le\frac{\log k}{\eta}+\frac{\eta}{2}\sum_j\widehat L_{n,j}.
--   $$
--
--   This combines the generic exponential-weights inequality with the exact Exp3-IX bias identity and is reusable independently of the probabilistic concentration analysis.
--
--   **Formalization Note** The theorem is pointwise and retains the empty-horizon boundary case.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020): Eq. (12.1), printed p. 165 / PDF p. 174, gives the deterministic exponential-weights loss estimate; Lemma 12.4, printed p. 169 / PDF p. 178, identifies the Exp3-IX bias. The statement combines them and specializes gamma = eta/2.

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.exp3ix_observed_loss_estimate_bound
    {k : ℕ} (hk : 1 < k) (n : ℕ) (η : ℝ) (hη : 0 < η)
    (h : BanditAlgorithm.BanditHistory k n)
    (hh : ∀ t : Fin n, (h t).2 ∈ Set.Icc (0 : ℝ) 1) (i : Fin k) :
    (∑ t : Fin n, (1 - (h t).2)) -
          (η / 2) *
            ∑ j : Fin k, BanditAlgorithm.exp3IXEstimate η (η / 2) n h j -
        BanditAlgorithm.exp3IXEstimate η (η / 2) n h i ≤
      Real.log k / η +
        (η / 2) *
          ∑ j : Fin k, BanditAlgorithm.exp3IXEstimate η (η / 2) n h j := by
  sorry

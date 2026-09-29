-- Prove2me | Theorems.Thm_BanditAlgorithm_adversarial_bandit_exp3ix_master_high_probability_regret
-- name    : BanditAlgorithm.adversarial_bandit_exp3ix_master_high_probability_regret
-- status  : Proved
-- author  : @jianglsbz
-- created : 2026-07-20T20:47:13.444694+00:00
-- url     : https://prove2.me/theorems/adf4dd95-743b-4795-8c83-4fec898fdca4
-- title:
--   Exp3-IX generic high-probability master bound
-- statement:
--   This is the generic high-probability master estimate for Exp3-IX.
--
--   Let there be $k>1$ arms and $n>0$ rounds, with an arbitrary reward table $x_{ti}\in[0,1]$. Fix $\delta\in(0,1)$ and a learning rate $\eta>0$, and run Exp3-IX with implicit-exploration parameter $\gamma=\eta/2$. Then the random regret $\widehat R_n$ obeys
--
--   $$
--   \mathbb P\!\left(\widehat R_n \ge \frac{\log k}{\eta} + \eta nk + \left(1+\frac1\eta\right)\log\frac{k+1}{\delta}\right) \le \delta.
--   $$
--
--   This is the reusable pre-specialization estimate in the proof of Theorem 12.1. The theorem and its two specialized conclusions (12.5)–(12.6) are printed on p. 167 / PDF p. 176. Lemma 12.2 is printed on p. 168 / PDF p. 177 and supplies the concentration input used in Lemma 12.3, Eq. (12.7). The final displayed estimate immediately before learning-rate substitution is printed on p. 169 / PDF p. 178, after Lemma 12.4. Choosing the two learning rates displayed in Theorem 12.1 yields the $\delta$-independent and $\delta$-tuned bounds, respectively.
--
--   **Formalization Note** The probability is represented as the `adversarialMeasure` of the bad set of length-$n$ histories, and the right side is embedded into the extended nonnegative reals.
-- source:
--   Lattimore and Szepesvari, Bandit Algorithms (CUP 2020): Theorem 12.1 and Eqs. (12.5)-(12.6), printed p. 167 / PDF p. 176; Lemma 12.2, printed p. 168 / PDF p. 177, as the concentration input to Lemma 12.3 Eq. (12.7); and the proof of Theorem 12.1, printed p. 169 / PDF p. 178, where Eq. (12.3), Lemma 12.3 Eq. (12.7), and Lemma 12.4 yield the displayed generic bound immediately before the paragraph substituting eta in {eta_1, eta_2}. The present statement specializes that display to gamma = eta/2.

import Definitions.Def_AdversarialBandit
import Definitions.Def_exp3Policy

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.adversarial_bandit_exp3ix_master_high_probability_regret
    {k : ℕ} (hk : 1 < k) (n : ℕ) (hn : 0 < n)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ i : Fin k, x t i ∈ Set.Icc (0 : ℝ) 1)
    (δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) 1)
    (η : ℝ) (hη : 0 < η)
    (π : BanditAlgorithm.BanditPolicy k)
    (hπ : BanditAlgorithm.IsExp3IXPolicy η (η / 2) π) :
    BanditAlgorithm.adversarialMeasure x π n
      {h : BanditAlgorithm.BanditHistory k n |
        Real.log k / η + η * (n * k) +
            (1 + 1 / η) * Real.log ((k + 1) / δ) ≤
          BanditAlgorithm.adversarialRandomRegret n x h} ≤
      ENNReal.ofReal δ := by
  sorry

-- Prove2me | Theorems.Thm_BanditAlgorithm_exp4_expected_potential_bound
-- name    : BanditAlgorithm.exp4_expected_potential_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T00:13:38.410949+00:00
-- url     : https://prove2.me/theorems/d7ed1887-8234-4d03-aca7-e9319ca8d996
-- title:
--   Exp4 expected potential bound
-- statement:
--   Let $k\ge1$, $M\ge2$, $n\ge1$, and $\eta>0$. Let rewards satisfy $x_{t,a}\in[0,1]$, let every expert advice row $(E_{t,m,a})_a$ be a probability distribution, and suppose the learner follows Exp4 with exploration parameter $\gamma=0$. Write $Q_{t,m}$ for the exponential weight of expert $m$, $\widetilde X_{t,m}$ for its one-round importance-weighted score, and
--
--   $$
--   V_n=\sum_{t=1}^{n}\sum_{j=1}^{M}Q_{t,j}(1-\widetilde X_{t,j})^2.
--   $$
--
--   For every fixed expert $m$,
--
--   $$
--   \mathbb E[\widetilde S_{n,m}]
--   -\mathbb E\!\left[\sum_{t=1}^{n}\sum_{j=1}^{M}Q_{t,j}\widetilde X_{t,j}\right]
--   \le \frac{\log M}{\eta}+\frac{\eta}{2}\,\mathbb E[V_n].
--   $$
--
--   This is the expected form of the exponential-weights potential inequality used in Exp4, before the mixture score and quadratic term are evaluated.
--
--   **Formalization Note** `exp4MixtureEstimate` is the cumulative double sum and `exp4QuadraticMass` is $V_n$; all expectations are integrals over the adversarial interaction measure.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Lemma 18.2 and Theorem 18.1 proof, printed p. 230, especially Eq. (18.9). https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_ContextualAdversarialBandit
import Definitions.Def_exp4Analysis

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.exp4_expected_potential_bound
    {k M : ℕ} (hk : 0 < k) (hM : 1 < M) (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (π : BanditPolicy k)
    (hπ : IsExp4Policy η 0 E π)
    (m : Fin M) :
    (∫ h, exp4Estimate η 0 E n h m ∂(adversarialMeasure x π n)) -
        (∫ h, exp4MixtureEstimate η E n h ∂(adversarialMeasure x π n)) ≤
      Real.log M / η +
        (η / 2) *
          (∫ h, exp4QuadraticMass η E n h ∂(adversarialMeasure x π n)) := by
  sorry

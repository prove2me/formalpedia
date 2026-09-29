-- Prove2me | Theorems.Thm_BanditAlgorithm_exp4_quadratic_mass_expectation_bound
-- name    : BanditAlgorithm.exp4_quadratic_mass_expectation_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T00:15:02.8027+00:00
-- url     : https://prove2.me/theorems/7634912b-68f3-4e09-b180-b01e578ba326
-- title:
--   Exp4 quadratic-mass expectation bound
-- statement:
--   Let $k\ge1$, $M\ge2$, $n\ge1$, and $\eta>0$. Let rewards satisfy $x_{t,a}\in[0,1]$, let every expert advice row be a probability distribution, and suppose the learner follows Exp4 with exploration parameter $\gamma=0$. With $Q_{t,m}$ and $\widetilde X_{t,m}$ denoting the Exp4 expert weights and one-round expert score estimates, define
--
--   $$
--   V_n=\sum_{t=1}^{n}\sum_{m=1}^{M}Q_{t,m}(1-\widetilde X_{t,m})^2.
--   $$
--
--   Then the cumulative quadratic term satisfies
--
--   $$
--   \mathbb E[V_n]\le nk.
--   $$
--
--   This second-moment estimate is the variance-control ingredient that turns the Exp4 potential inequality into a square-root regret bound.
--
--   **Formalization Note** $V_n$ is represented by `exp4QuadraticMass`, recursively accumulated along the sampled bandit history.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), Theorem 18.1 proof, printed p. 230, Eq. (18.12) and the displayed calculation immediately below it. https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_ContextualAdversarialBandit
import Definitions.Def_exp4Analysis

open MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.exp4_quadratic_mass_expectation_bound
    {k M : ℕ} (hk : 0 < k) (hM : 1 < M) (n : ℕ) (hn : 0 < n)
    (η : ℝ) (hη : 0 < η)
    (x : ℕ → Fin k → ℝ) (hx : ∀ t : ℕ, ∀ a : Fin k, x t a ∈ Set.Icc (0 : ℝ) 1)
    (E : ℕ → Fin M → Fin k → ℝ)
    (hE0 : ∀ t : ℕ, ∀ m : Fin M, ∀ a : Fin k, 0 ≤ E t m a)
    (hE1 : ∀ t : ℕ, ∀ m : Fin M, ∑ a, E t m a = 1)
    (π : BanditPolicy k)
    (hπ : IsExp4Policy η 0 E π) :
    (∫ h, exp4QuadraticMass η E n h ∂(adversarialMeasure x π n)) ≤
      (n : ℝ) * k := by
  sorry

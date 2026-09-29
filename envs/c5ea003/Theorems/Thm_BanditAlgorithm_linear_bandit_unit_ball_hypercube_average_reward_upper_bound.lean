-- Prove2me | Theorems.Thm_BanditAlgorithm_linear_bandit_unit_ball_hypercube_average_reward_upper_bound
-- name    : BanditAlgorithm.linear_bandit_unit_ball_hypercube_average_reward_upper_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T19:54:53.337706+00:00
-- url     : https://prove2.me/theorems/1ca86277-b345-40b5-b96b-0f28e8d944e1
-- title:
--   Average reward bound for the Rademacher unit-ball linear bandit
-- statement:
--   Let $d,n$ be positive and let $\pi$ be any stochastic linear-bandit policy
--   supported on the Euclidean unit ball. Put
--
--   $$
--   \Delta=\sqrt{\frac{d}{48n}}
--   $$
--
--   and, for each Boolean sign vector $\sigma\in\{-1,1\}^d$, define
--   $\theta_\sigma=\Delta\sigma$. Then the total expected reward, summed over the
--   entire sign cube, satisfies
--
--   $$
--   \sum_{\sigma\in\{-1,1\}^d}
--   \mathbb E_{\theta_\sigma}
--   \left[\sum_{t=1}^n\langle A_t,\theta_\sigma\rangle\right]
--   \le
--   2^d\,n\Delta^2\sqrt n.
--   $$
--
--   Equivalently, under the uniform Rademacher prior, the expected cumulative
--   reward is at most $n\Delta^2\sqrt n$.
--
--   The information-theoretic proof pairs environments differing in one sign.
--   For a square-integrable action coordinate $g$, Cauchy--Schwarz and the
--   pointwise inequality
--
--   $$
--   (x-y)\log(x/y)\ge \frac{2(x-y)^2}{x+y}
--   $$
--
--   control the squared difference of the two expected actions by their
--   symmetrized Kullback--Leibler divergence times their second action moment.
--   The adaptive Gaussian chain rule gives the exact coordinate-flip divergence
--   $2\Delta^2\mathbb E\sum_{s<t}A_{s,i}^2$. Two applications of
--   Cauchy--Schwarz, together with $\|A_t\|_2\le1$, then bound the average reward
--   at round $t$ by $\Delta^2\sqrt t$. Summing and using
--   $\sum_{t<n}\sqrt t\le n\sqrt n$ proves the displayed inequality.
--
--   **Source note.** This is an alternative, source-correct information-theoretic
--   lemma for Lattimore--Szepesvári, Theorem 24.2. Its Gaussian divergence step is
--   the general-action decomposition of Exercise 15.8 applied to the
--   coordinate-flip pair. It deliberately avoids the normalization discrepancy
--   in the printed equation (24.3).
-- source:
--   Alternative lemma for Lattimore and Szepesvári, Bandit Algorithms (2020), Theorem 24.2, pp. 290–291. The exact general-action Gaussian divergence input is Exercise 15.8, p. 209; the proof uses symmetrized KL and deliberately avoids the factor-of-two discrepancy in displayed Eq. (24.3).

import Definitions.Def_LinearBanditProtocol

open Matrix MeasureTheory

theorem BanditAlgorithm.linear_bandit_unit_ball_hypercube_average_reward_upper_bound
    {d n : ℕ} (hd : 0 < d) (hn : 0 < n)
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    let Δ := Real.sqrt ((d : ℝ) / (48 * n))
    (∑ σ : Fin d → Bool,
        ∫ h, ∑ t, (h t).1 ⬝ᵥ
          (fun i ↦ Δ * if σ i then 1 else -1)
          ∂linearBanditMeasure
            (fun i ↦ Δ * if σ i then 1 else -1) π n) ≤
      (Fintype.card (Fin d → Bool) : ℝ) *
        (n * Δ ^ 2 * Real.sqrt n) := by
  sorry

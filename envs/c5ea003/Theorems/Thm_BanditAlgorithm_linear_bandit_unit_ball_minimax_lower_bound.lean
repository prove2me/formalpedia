-- Prove2me | Theorems.Thm_BanditAlgorithm_linear_bandit_unit_ball_minimax_lower_bound
-- name    : BanditAlgorithm.linear_bandit_unit_ball_minimax_lower_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T16:53:39.218591+00:00
-- url     : https://prove2.me/theorems/54a2de15-e776-4096-b974-f94503b30d78
-- statement:
--   (Unit-ball lower bound, GOAL, L&S Theorem 24.2) Assume $d \le 2n$ and let $\mathcal{A} = \{x \in \mathbb{R}^d : \|x\|_2 \le 1\}$, with unit-variance Gaussian noise. Then, for any policy supported in $\mathcal{A}$, there exists a parameter $\theta \in \mathbb{R}^d$ with $\|\theta\|_2^2 = \frac{d^2}{48n}$ such that
--
--   $$R_n(\mathcal{A},\theta) \ge \frac{d\sqrt{n}}{16\sqrt{3}}.$$
--
--   (The book's explicit condition is $d \le 2n$, not $n \ge d^2$.)
-- source:
--   L&S Theorem 24.2, p.290

import Definitions.Def_LinearBanditProtocol


open Matrix MeasureTheory

theorem BanditAlgorithm.linear_bandit_unit_ball_minimax_lower_bound {d n : ℕ}
    (hd : 0 < d) (hdn : d ≤ 2 * n) (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π) :
    ∃ θ : Fin d → ℝ, θ ⬝ᵥ θ = (d : ℝ) ^ 2 / (48 * n) ∧
      d * Real.sqrt n / (16 * Real.sqrt 3) ≤
        linearBanditExpectedRegret {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} θ π n := by
  sorry

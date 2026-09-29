-- Prove2me | Theorems.Thm_BanditAlgorithm_linear_bandit_unit_ball_stopped_loss_change_of_measure
-- name    : BanditAlgorithm.linear_bandit_unit_ball_stopped_loss_change_of_measure
-- status  : Open
-- author  : @Harry_Xu
-- created : 2026-07-29T18:28:18.194113+00:00
-- url     : https://prove2.me/theorems/414253b3-f121-4611-84a2-a939ec039c9e
-- title:
--   Stopped loss change of measure for the unit-ball linear bandit
-- statement:
--   Let $d,n$ be positive integers with $d\le 2n$, let $\pi$ be a stochastic
--   linear-bandit policy supported on the Euclidean unit ball, and set
--
--   $$
--   \Delta=\sqrt{\frac{d}{48n}}.
--   $$
--
--   Fix a sign vector $\sigma\in\{-1,1\}^d$ and a coordinate $i$. Write
--   $\theta=\Delta\sigma$, let $\sigma^{(i)}$ be obtained by flipping the $i$th
--   sign, and put $\theta'=\Delta\sigma^{(i)}$.
--
--   For a history $h=(A_1,X_1,\ldots,A_n,X_n)$, call round $t$ active when
--
--   $$
--   \sum_{s<t}A_{s,i}^2<\frac nd,
--   $$
--
--   and define the stopped coordinate loss
--
--   $$
--   U_i(x;h)=
--   \sum_{t=1}^n
--   \mathbf 1\!\left\{\sum_{s<t}A_{s,i}^2<\frac nd\right\}
--   \left(\frac1{\sqrt d}-A_{t,i}x\right)^2.
--   $$
--
--   Then the expectations under the two adaptive Gaussian interaction laws obey
--
--   $$
--   \mathbb E_{\theta'}[U_i(\sigma_i)]
--   -
--   \frac{\Delta}{2}
--   \left(\frac{4n}{d}+2\right)
--   \sqrt{\frac nd+1}
--   \le
--   \mathbb E_{\theta}[U_i(\sigma_i)].
--   $$
--
--   This is the stopped change-of-measure inequality displayed in the
--   coordinatewise testing argument of the cited source.
--
--   **Source-normalization warning.** With unit-variance Gaussian noise, flipping
--   the coordinate from $+\Delta$ to $-\Delta$ changes the conditional mean by
--   $2\Delta A_{t,i}$, whose one-step Kullback--Leibler divergence is
--   $2\Delta^2A_{t,i}^2$. Consequently, the ordinary Pinsker inequality and
--   Exercise 15.7 by themselves yield a correction with coefficient $\Delta$,
--   not the $\Delta/2$ printed in equation (24.3). Thus the statement above
--   isolates exactly the sharper step required by the printed proof; it should
--   not be regarded as already justified by the cited chain rule alone.
--
--   **Formalization note.** The indicator tests the energy strictly before round
--   $t$. Thus the sum includes the first threshold-crossing action, matching the
--   capped stopping time used in the source.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (2020), Theorem 24.2, pp. 290–291, displayed equations (24.3)–(24.4). Normalization warning: for unit-variance noise and a ±Δ coordinate flip, Exercise 15.7 gives one-step KL 2Δ²A_{t,i}², so ordinary Pinsker produces coefficient Δ rather than the printed Δ/2; an additional sharper argument is required.

import Definitions.Def_LinearBanditProtocol

open Matrix MeasureTheory

theorem BanditAlgorithm.linear_bandit_unit_ball_stopped_loss_change_of_measure
    {d n : ℕ} (hd : 0 < d) (hdn : d ≤ 2 * n)
    (π : LinearBanditPolicy d)
    (hsupp : IsSupportedLinearPolicy
      {a : Fin d → ℝ | a ⬝ᵥ a ≤ 1} π)
    (σ : Fin d → Bool) (i : Fin d) :
    let Δ := Real.sqrt ((d : ℝ) / (48 * n))
    let sign : Fin d → ℝ := fun j ↦ if σ j then 1 else -1
    let θ : Fin d → ℝ := fun j ↦ Δ * sign j
    let σ' : Fin d → Bool := Function.update σ i (!(σ i))
    let sign' : Fin d → ℝ := fun j ↦ if σ' j then 1 else -1
    let θ' : Fin d → ℝ := fun j ↦ Δ * sign' j
    let active : LinearBanditHistory d n → Fin n → Prop := fun h t ↦
      (∑ s ∈ Finset.univ.filter (fun s : Fin n ↦ s < t),
          ((h s).1 i) ^ 2) < (n : ℝ) / d
    let U : LinearBanditHistory d n → ℝ → ℝ := fun h x ↦
      ∑ t, if active h t then
        (1 / Real.sqrt d - (h t).1 i * x) ^ 2 else 0
    (∫ h, U h (sign i) ∂linearBanditMeasure θ' π n) -
        (Δ / 2) * (4 * (n : ℝ) / d + 2) *
          Real.sqrt ((n : ℝ) / d + 1) ≤
      ∫ h, U h (sign i) ∂linearBanditMeasure θ π n := by
  sorry

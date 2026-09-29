-- Prove2me | Theorems.Thm_BanditAlgorithm_linear_bandit_unit_ball_coordinate_flip_stopped_loss_lower_bound
-- name    : BanditAlgorithm.linear_bandit_unit_ball_coordinate_flip_stopped_loss_lower_bound
-- status  : Proved
-- author  : @Harry_Xu
-- created : 2026-07-29T18:17:53.861375+00:00
-- url     : https://prove2.me/theorems/24f842fc-c0a1-4d29-912c-02d4523426a8
-- title:
--   Coordinate-flip stopped-loss lower bound for unit-ball linear bandits
-- statement:
--   Let $d,n$ be positive integers with $d\le 2n$, let $\pi$ be a stochastic linear-bandit policy supported on the Euclidean unit ball, and put
--
--   $$
--   \Delta=\sqrt{\frac{d}{48n}}.
--   $$
--
--   Fix a sign vector $\sigma\in\{-1,1\}^d$ and a coordinate $i$. Let $\sigma^{(i)}$ be obtained by flipping only the $i$th sign, and set $\theta=\Delta\sigma$ and $\theta'=\Delta\sigma^{(i)}$.
--
--   For a history $h=(A_1,X_1,\ldots,A_n,X_n)$, retain round $t$ while the coordinate energy accumulated strictly before that round is below $n/d$:
--
--   $$
--   \sum_{s<t}A_{s,i}^2<\frac nd.
--   $$
--
--   For $x\in\{-1,1\}$ define the corresponding stopped squared loss
--
--   $$
--   U_i(x;h)=
--   \sum_{t=1}^n
--   \mathbf 1\!\left\{\sum_{s<t}A_{s,i}^2<\frac nd\right\}
--   \left(\frac1{\sqrt d}-A_{t,i}x\right)^2.
--   $$
--
--   Writing $\mathbb E_\theta$ and $\mathbb E_{\theta'}$ for expectation under the two Gaussian linear-bandit interaction laws, the coordinate-flip pair satisfies
--
--   $$
--   \mathbb E_\theta[U_i(\sigma_i)]
--   +
--   \mathbb E_{\theta'}[U_i(\sigma_i^{(i)})]
--   \ge \frac nd.
--   $$
--
--   This is the coordinatewise testing estimate used by the randomisation argument for the unit-ball minimax lower bound. It isolates the reusable stopped change-of-measure core from the subsequent finite hypercube averaging.
--
--   **Formalization Note** A round is active according to energy strictly before it, which is equivalent to summing through the capped first threshold-crossing round in the source. Boolean values encode the two signs.
-- source:
--   Lattimore and Szepesvári, Bandit Algorithms (Cambridge University Press, 2020), proof of Theorem 24.2, pp. 290–291, Eqs. (24.3)–(24.5) and the immediately following paired-loss display; https://tor-lattimore.com/downloads/book/book.pdf

import Definitions.Def_LinearBanditProtocol

open Matrix MeasureTheory

theorem BanditAlgorithm.linear_bandit_unit_ball_coordinate_flip_stopped_loss_lower_bound
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
    (n : ℝ) / d ≤
      (∫ h, U h (sign i) ∂linearBanditMeasure θ π n) +
      ∫ h, U h (sign' i) ∂linearBanditMeasure θ' π n := by
  sorry

-- Prove2me | Theorems.Thm_BanditAlgorithm_adversarial_linear_bandit_ftrl_unit_ball_regret_indep_seeds
-- name    : BanditAlgorithm.adversarial_linear_bandit_ftrl_unit_ball_regret_indep_seeds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T18:22:16.793583+00:00
-- url     : https://prove2.me/theorems/fc1a51fe-f8e4-4371-a729-df8a653904e1
-- title:
--   Theorem 28.11: FTRL unit-ball bandit regret $2\sqrt{3nd\log n}$ (corrected root)
-- statement:
--   (Adversarial linear bandit on the unit ball, GOAL, Theorem 28.11; corrected root — supersedes `BanditAlgorithm.adversarial_linear_bandit_ftrl_unit_ball_regret`, whose hypotheses omitted the within-round independence of the two seeds.) Fix oblivious losses $\|y_t\|_2 \le 1$, $2 \le n$, and action set the Euclidean unit ball. On a probability space carrying per-round seeds $V_t \sim \mathrm{Unif}[0,1]$ and $W_t \sim \mathrm{Unif}(\{\pm e_1,\ldots,\pm e_d\})$ such that the pairs $(V_t, W_t)$ are mutually independent across rounds **and, within each round, $V_t$ is independent of $W_t$** — so the $2n$ seeds are jointly independent, exactly as Algorithm 17 samples the exploration bit and the direction $U_t$ separately — Algorithm 16/17 runs FTRL with the Legendre potential
--
--   $$F(a) = -\log(1-\|a\|) - \|a\|$$
--
--   on the shrunken ball of radius $r = 1 - 2\eta d > 0$ with $\eta = \sqrt{\log(n)/(3dn)}$: with exploration indicator $E_t = \mathbb{1}\{V_t < 1-\|\bar A_t\|\}$ it plays
--
--   $$A_t = E_t U_t + (1-E_t)\frac{\bar A_t}{\|\bar A_t\|}$$
--
--   and feeds FTRL the one-point importance-weighted estimator (Eq. (28.12))
--
--   $$\hat Y_t = \frac{d\, E_t\, \langle A_t, y_t\rangle}{1-\|\bar A_t\|}\, A_t.$$
--
--   Then the expected regret satisfies
--
--   $$\mathbb{E}\Big[\sum_{t<n}\langle A_t - a_0, y_t\rangle\Big] \le 2\sqrt{3 n d \log n}$$
--
--   for every comparator $a_0$ in the unit ball.
--
--   The within-round independence hypothesis is used exactly once in the source proof: it makes $\hat Y_t$ conditionally unbiased given the past (the sentence after Eq. (28.12)), which is what allows the FTRL master bound (Theorem 28.10) to be applied to the estimated losses.
-- source:
--   L&S Theorem 28.11, p.338

import Definitions.Def_OnlineLinearOptimization
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic


open RealInnerProductSpace MeasureTheory ProbabilityTheory

theorem BanditAlgorithm.adversarial_linear_bandit_ftrl_unit_ball_regret_indep_seeds
    (d n : ℕ) (hd : 0 < d) (hn : 2 ≤ n)
    (y : ℕ → EuclideanSpace ℝ (Fin d)) (hy : ∀ t, ‖y t‖ ≤ 1)
    (η r : ℝ)
    (hη : η = Real.sqrt (Real.log n / (3 * d * n)))
    (hr : r = 1 - 2 * η * d) (hr0 : 0 < r)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (V : ℕ → Ω → ℝ) (W : ℕ → Ω → Fin d × Bool)
    (hVmeas : ∀ t, Measurable (V t)) (hWmeas : ∀ t, Measurable (W t))
    (hindep : iIndepFun (fun t ω => (V t ω, W t ω)) P)
    (hVW : ∀ t, IndepFun (V t) (W t) P)
    (hV : ∀ t, Measure.map (V t) P = (volume : Measure ℝ).restrict (Set.Icc 0 1))
    (hW : ∀ t (u : Fin d × Bool), P {ω | W t ω = u} = ((2 * d : ℕ) : ENNReal)⁻¹)
    (Abar A Yhat : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hftrl : ∀ ω, IsFTRLIterates η
      (fun b : EuclideanSpace ℝ (Fin d) => -Real.log (1 - ‖b‖) - ‖b‖)
      (Metric.ball 0 1) (Metric.closedBall 0 r)
      (fun t => Yhat t ω) (fun t => Abar t ω))
    (hA : ∀ t ω, A t ω =
      if V t ω < 1 - ‖Abar t ω‖ then
        (if (W t ω).2 then (1 : ℝ) else -1) • EuclideanSpace.single (W t ω).1 1
      else ‖Abar t ω‖⁻¹ • Abar t ω)
    (hY : ∀ t ω, Yhat t ω =
      (if V t ω < 1 - ‖Abar t ω‖ then
        d * ⟪A t ω, y t⟫ / (1 - ‖Abar t ω‖) else 0) • A t ω) :
    ∀ a₀ ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      ∫ ω, oloRegret (fun t => A t ω) y n a₀ ∂P ≤
        2 * Real.sqrt (3 * n * d * Real.log n) := by
  sorry

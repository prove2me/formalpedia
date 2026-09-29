-- Prove2me | solution 1 for BanditAlgorithm.adversarial_linear_bandit_ftrl_unit_ball_regret_indep_seeds
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-30T01:33:38.757024+00:00
-- url     : https://prove2.me/submissions/210ecdee-fc50-44a9-90b4-9ba5ef031278

import Theorems.Thm_BanditAlgorithm_adversarial_linear_bandit_ftrl_unit_ball_regret_untuned
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

open RealInnerProductSpace MeasureTheory ProbabilityTheory
open BanditAlgorithm

theorem solution
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
  have hnR : (1 : ℝ) < n := by
    exact_mod_cast (show 1 < n by omega)
  have hnR0 : 0 < (n : ℝ) := by positivity
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos hnR
  have hden : 0 < (3 : ℝ) * d * n := by positivity
  have hquot : 0 < Real.log (n : ℝ) / ((3 : ℝ) * d * n) :=
    div_pos hlog hden
  have hη0 : 0 < η := by
    rw [hη]
    exact Real.sqrt_pos.2 hquot
  have hηsq :
      η ^ 2 = Real.log (n : ℝ) / ((3 : ℝ) * d * n) := by
    rw [hη, Real.sq_sqrt (le_of_lt hquot)]
  have hr1 : r < 1 := by
    rw [hr]
    have : 0 < 2 * η * (d : ℝ) := by positivity
    linarith
  have hloghalf : (1 / 2 : ℝ) < Real.log (n : ℝ) := by
    have h2n : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog2n : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) :=
      Real.log_le_log (by positivity) h2n
    linarith [Real.log_two_gt_d9]
  have hone_le : (1 : ℝ) ≤ 2 * η * d * n := by
    have hsquare :
        1 < (2 * η * (d : ℝ) * n) ^ 2 := by
      rw [show (2 * η * (d : ℝ) * n) ^ 2 =
        4 * (η ^ 2) * d ^ 2 * n ^ 2 by ring, hηsq]
      field_simp
      nlinarith [show (1 : ℝ) ≤ d by exact_mod_cast hd,
        show (2 : ℝ) ≤ n by exact_mod_cast hn]
    have hpos : 0 < 2 * η * (d : ℝ) * n := by positivity
    nlinarith [sq_nonneg (2 * η * (d : ℝ) * n - 1)]
  have hargle : 1 / (1 - r) ≤ (n : ℝ) := by
    have hp : 0 < 1 - r := by linarith
    rw [div_le_iff₀ hp]
    rw [hr]
    nlinarith
  have hlogle :
      Real.log (1 / (1 - r)) ≤ Real.log (n : ℝ) := by
    exact Real.log_le_log (by positivity) hargle
  have hsqrt :
      Real.sqrt ((3 : ℝ) * n * d * Real.log n) =
        3 * η * n * d := by
    have hrad :
        (3 : ℝ) * n * d * Real.log n =
          (3 * η * n * d) ^ 2 := by
      rw [show (3 * η * (n : ℝ) * d) ^ 2 =
        9 * (η ^ 2) * n ^ 2 * d ^ 2 by ring, hηsq]
      field_simp
      ring
    rw [hrad, Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  intro a₀ ha₀
  have hcore :=
    BanditAlgorithm.adversarial_linear_bandit_ftrl_unit_ball_regret_untuned
      d n hd hn y hy η r hη0 hr hr0 P V W hVmeas hWmeas
      hindep hVW hV hW Abar A Yhat hftrl hA hY a₀ ha₀
  have hlogterm :
      Real.log (1 / (1 - r)) / η ≤ 3 * η * n * d := by
    rw [div_le_iff₀ hη0]
    calc
      Real.log (1 / (1 - r)) ≤ Real.log (n : ℝ) := hlogle
      _ = (3 * η * n * d) * η := by
        rw [show (3 * η * (n : ℝ) * d) * η =
          3 * (η ^ 2) * n * d by ring, hηsq]
        field_simp
  rw [hsqrt]
  rw [hr] at hcore hlogterm
  nlinarith

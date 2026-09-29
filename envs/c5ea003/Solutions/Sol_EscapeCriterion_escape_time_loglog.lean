-- Prove2me | solution 1 for EscapeCriterion.escape_time_loglog
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:31:54.491179+00:00
-- url     : https://prove2.me/submissions/01596ec3-8e24-405d-aabb-440656601502

-- Sol generated from Novelty/EscapeDoublyExponential.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeDoublyExponential
import Definitions.Def_Novelty_EscapeRateGreenFunction
import Theorems.Thm_EscapeCriterion_log_norm_orbit_sub_one_ge
import Theorems.Thm_EscapeCriterion_two_lt_norm_orbit

/-!
# Doubly exponential escape, sharp potential bounds, and the Douady–Hubbard potential

Third iteration of the escape-criterion thread. The geometric bound of
`EscapeCriterion.escape_norm_growth` (`‖z_n‖ ≥ (‖z‖-1)^n ‖z‖`) is exponentially weaker than
the truth; combining it with the logarithmic distortion estimate of
`EscapeCriterion.log_distortion` upgrades it to the correct **doubly exponential** rate.

Main results:

* `log_norm_orbit_sub_one_ge`: `log ‖z_n‖ - 1 ≥ 2ⁿ (log ‖z‖ - 1)`.
* `norm_orbit_ge_exp`: `‖z_n‖ ≥ exp(2ⁿ (log ‖z‖ - 1) + 1)`.
* `escape_time_loglog`: the escape-time test terminates after `O(log log B)` iterations —
  exponentially better than the Bernoulli bound `escape_time_bound`.
* `abs_escapeRate_sub_log_le_two_div`: the sharp a priori estimate
  `|G_c(z) - log ‖z‖| ≤ 2/‖z‖`, whence `escapeRate_asymptotic`:
  `G_c(z) = log ‖z‖ + O(1/‖z‖)` uniformly in `c`.
* `mandelbrotPotential`: the Douady–Hubbard potential `G_M(c) = lim 2^{-n} log ‖z_n(c)‖` of
  the exterior of the Mandelbrot set, shown to exist and to be positive for `‖c‖ > 2`,
  with the explicit lower bound `mandelbrotPotential_ge`.
-/

open EscapeCriterion

open Filter MandelbrotEscape
open scoped Topology

variable {c z : ℂ}

/-! ## Doubly exponential growth -/





/-! ## The sharp a priori bound for the escape rate -/




/-! ## The Douady–Hubbard potential of the Mandelbrot exterior -/







open EscapeCriterion in
theorem solution(hz : escapeRadius c < ‖z‖) (h3 : 3 ≤ ‖z‖) {B : ℝ} (hB : 0 < B)
    {n : ℕ} (hn : (Real.log B - 1) / (Real.log ‖z‖ - 1) ≤ 2 ^ n) : B ≤ ‖orbit c z n‖ := by
  have hlog3 : 1 < Real.log ‖z‖ := by
    have h1 : Real.log 3 ≤ Real.log ‖z‖ := Real.log_le_log (by norm_num) h3
    have h2 : (1 : ℝ) < Real.log 3 := by
      rw [show (1 : ℝ) = Real.log (Real.exp 1) by simp]
      exact Real.log_lt_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    linarith
  have hden : (0 : ℝ) < Real.log ‖z‖ - 1 := by linarith
  have hmul : Real.log B - 1 ≤ 2 ^ n * (Real.log ‖z‖ - 1) := by
    rw [div_le_iff₀ hden] at hn
    linarith [hn]
  have hposn : (0 : ℝ) < ‖orbit c z n‖ := by linarith [two_lt_norm_orbit hz n]
  have hgrow := log_norm_orbit_sub_one_ge hz n
  have : Real.log B ≤ Real.log ‖orbit c z n‖ := by linarith
  exact (Real.log_le_log_iff hB hposn).mp this

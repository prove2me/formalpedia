-- Prove2me | solution 1 for EscapeCriterion.dist_logOrbitSeq_le_two_div
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:16:17.120062+00:00
-- url     : https://prove2.me/submissions/4545ea3c-bfdd-4055-bff5-b9f52fee7516

-- Sol generated from Novelty/EscapeDoublyExponential.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeDoublyExponential
import Definitions.Def_Novelty_EscapeRateGreenFunction
import Theorems.Thm_EscapeCriterion_abs_log_orbit_succ_sub
import Theorems.Thm_EscapeCriterion_escape_norm_growth
import Theorems.Thm_EscapeCriterion_two_le_escapeRadius

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

lemma norm_le_norm_orbit (hz : escapeRadius c < ‖z‖) (n : ℕ) : ‖z‖ ≤ ‖orbit c z n‖ := by
  have h2 : (2 : ℝ) < ‖z‖ := lt_of_le_of_lt (two_le_escapeRadius c) hz
  have hone : (1 : ℝ) ≤ (‖z‖ - 1) ^ n := one_le_pow₀ (by linarith)
  have hg := (escape_norm_growth c z hz n).2
  nlinarith [norm_nonneg z]




/-! ## The sharp a priori bound for the escape rate -/




/-! ## The Douady–Hubbard potential of the Mandelbrot exterior -/







open EscapeCriterion in
theorem solution(hz : escapeRadius c < ‖z‖) (n : ℕ) :
    dist (logOrbitSeq c z n) (logOrbitSeq c z (n + 1)) ≤ (2 / ‖z‖) * (1 / 2 : ℝ) ^ (n + 1) := by
  have hzpos : (0 : ℝ) < ‖z‖ := by linarith [lt_of_le_of_lt (two_le_escapeRadius c) hz]
  have hmono : 2 / ‖orbit c z n‖ ≤ 2 / ‖z‖ :=
    div_le_div_of_nonneg_left (by norm_num) hzpos (norm_le_norm_orbit hz n)
  have hkey := abs_log_orbit_succ_sub hz n
  have hpowpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  rw [Real.dist_eq, logOrbitSeq, logOrbitSeq]
  have hexpand :
      Real.log ‖orbit c z n‖ / 2 ^ n - Real.log ‖orbit c z (n + 1)‖ / 2 ^ (n + 1)
        = -(Real.log ‖orbit c z (n + 1)‖ - 2 * Real.log ‖orbit c z n‖) / 2 ^ (n + 1) := by
    field_simp
    ring
  rw [hexpand, abs_div, abs_neg, abs_of_pos hpowpos, div_le_iff₀ hpowpos]
  have hone : (2 / ‖z‖) * (1 / 2 : ℝ) ^ (n + 1) * 2 ^ (n + 1) = 2 / ‖z‖ := by
    rw [div_pow, one_pow]
    field_simp
  rw [hone]
  exact le_trans hkey hmono

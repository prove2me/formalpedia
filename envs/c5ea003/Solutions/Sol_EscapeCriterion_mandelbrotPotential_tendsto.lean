-- Prove2me | solution 1 for EscapeCriterion.mandelbrotPotential_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:31:56.209621+00:00
-- url     : https://prove2.me/submissions/63b21a51-a81a-4355-a64a-0cbd0df8ebae

-- Sol generated from Novelty/EscapeDoublyExponential.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeDoublyExponential
import Definitions.Def_Novelty_EscapeRateGreenFunction
import Definitions.Def_Novelty_MandelbrotQuadraticEscape
import Theorems.Thm_EscapeCriterion_critOrbit_eq_orbit
import Theorems.Thm_EscapeCriterion_escapeRadius_lt_norm_critOrbit_two
import Theorems.Thm_EscapeCriterion_escapeRate_tendsto
import Theorems.Thm_EscapeCriterion_orbit_add

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
theorem solution(hc : 2 < ‖c‖) :
    Filter.Tendsto (fun n => Real.log ‖critOrbit c (n + 1)‖ / 2 ^ n) Filter.atTop
      (𝓝 (mandelbrotPotential c)) := by
  have hz2 : escapeRadius c < ‖orbit c 0 2‖ := escapeRadius_lt_norm_critOrbit_two hc
  have hshift := escapeRate_tendsto hz2
  have hscaled : Filter.Tendsto (fun n => logOrbitSeq c (orbit c 0 2) n / 2) Filter.atTop
      (𝓝 (mandelbrotPotential c)) := by
    simpa [mandelbrotPotential] using hshift.div_const 2
  rw [← Filter.tendsto_add_atTop_iff_nat 1]
  refine Filter.Tendsto.congr (fun n => ?_) hscaled
  rw [logOrbitSeq, critOrbit_eq_orbit, ← orbit_add]
  have hidx : n + 1 + 1 = 2 + n := by omega
  rw [hidx, pow_succ]
  field_simp

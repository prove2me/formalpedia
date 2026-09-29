-- Prove2me | Definitions.Def_Novelty_EscapeDoublyExponential
-- name    : Novelty_EscapeDoublyExponential
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:23:41.850203+00:00
-- url     : https://prove2.me/theorems/c4055b96-1fc0-478e-aa5c-388c6d3f1d67
-- title:
--   Aether Catalog definitions — Novelty_EscapeDoublyExponential
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EscapeDoublyExponential`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EscapeDoublyExponential.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeRateGreenFunction

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

namespace EscapeCriterion

open Filter MandelbrotEscape
open scoped Topology

variable {c z : ℂ}

/-! ## Doubly exponential growth -/





/-! ## The sharp a priori bound for the escape rate -/




/-! ## The Douady–Hubbard potential of the Mandelbrot exterior -/


/-- The **Douady–Hubbard potential** of the exterior of the Mandelbrot set:
`G_M(c) = G_c(c) = lim 2^{-n} log ‖f_c^n(c)‖`, i.e. the escape rate of the critical *value*
`c`. It is computed here through the (strictly escaping) second critical-orbit point. -/
noncomputable def mandelbrotPotential (c : ℂ) : ℝ := escapeRate c (orbit c 0 2) / 2




end EscapeCriterion



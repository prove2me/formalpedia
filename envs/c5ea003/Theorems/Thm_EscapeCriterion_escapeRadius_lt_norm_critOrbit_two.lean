-- Prove2me | Theorems.Thm_EscapeCriterion_escapeRadius_lt_norm_critOrbit_two
-- name    : EscapeCriterion.escapeRadius_lt_norm_critOrbit_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:42:53.714215+00:00
-- url     : https://prove2.me/theorems/cea47266-a1dc-4381-a8be-de969faebf82
-- title:
--   For `‖c‖ > 2` the second point of the critical orbit is strictly outside the escape
-- statement:
--   For `‖c‖ > 2` the second point of the critical orbit is strictly outside the escape
--   radius (the first one, `c` itself, only meets it).
--
--   ```lean
--   theorem EscapeCriterion.escapeRadius_lt_norm_critOrbit_two(hc : 2 < ‖c‖) :
--       escapeRadius c < ‖orbit c 0 2‖ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EscapeDoublyExponential.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EscapeDoublyExponential.lean#L149

-- Thm stub generated from Novelty/EscapeDoublyExponential.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeDoublyExponential
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

open EscapeCriterion

open Filter MandelbrotEscape
open scoped Topology

variable {c z : ℂ}

/-! ## Doubly exponential growth -/





/-! ## The sharp a priori bound for the escape rate -/




/-! ## The Douady–Hubbard potential of the Mandelbrot exterior -/

theorem EscapeCriterion.escapeRadius_lt_norm_critOrbit_two(hc : 2 < ‖c‖) :
    escapeRadius c < ‖orbit c 0 2‖ := by sorry

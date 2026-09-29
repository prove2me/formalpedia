-- Prove2me | Theorems.Thm_EscapeCriterion_escape_time_loglog
-- name    : EscapeCriterion.escape_time_loglog
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:43:45.138205+00:00
-- url     : https://prove2.me/theorems/ce4bafb9-8d66-4ab6-b48e-81ef95ab1f83
-- title:
--   Log-log escape time.
-- statement:
--   **Log-log escape time.** Starting from `‖z‖ ≥ 3`, the orbit exceeds the threshold `B`
--   after `n` iterations as soon as `2ⁿ ≥ (log B - 1)/(log ‖z‖ - 1)`; i.e. `O(log log B)`
--   iterations suffice, in contrast with the `O(B)` Bernoulli bound `escape_time_bound`.
--
--   ```lean
--   theorem EscapeCriterion.escape_time_loglog(hz : escapeRadius c < ‖z‖) (h3 : 3 ≤ ‖z‖) {B : ℝ} (hB : 0 < B)
--       {n : ℕ} (hn : (Real.log B - 1) / (Real.log ‖z‖ - 1) ≤ 2 ^ n) : B ≤ ‖orbit c z n‖ := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EscapeDoublyExponential.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EscapeDoublyExponential.lean#L68

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

theorem EscapeCriterion.escape_time_loglog(hz : escapeRadius c < ‖z‖) (h3 : 3 ≤ ‖z‖) {B : ℝ} (hB : 0 < B)
    {n : ℕ} (hn : (Real.log B - 1) / (Real.log ‖z‖ - 1) ≤ 2 ^ n) : B ≤ ‖orbit c z n‖ := by sorry

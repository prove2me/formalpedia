-- Prove2me | Theorems.Thm_EscapeCriterion_dist_logOrbitSeq_le_two_div
-- name    : EscapeCriterion.dist_logOrbitSeq_le_two_div
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:42:43.291077+00:00
-- url     : https://prove2.me/theorems/41945681-2eca-4469-a0a2-9b3d402c15e0
-- title:
--   Dist logOrbitSeq le two div
-- statement:
--   Formal statement of `EscapeCriterion.dist_logOrbitSeq_le_two_div` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem EscapeCriterion.dist_logOrbitSeq_le_two_div(hz : escapeRadius c < ‖z‖) (n : ℕ) :
--       dist (logOrbitSeq c z n) (logOrbitSeq c z (n + 1)) ≤ (2 / ‖z‖) * (1 / 2 : ℝ) ^ (n + 1) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EscapeDoublyExponential.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EscapeDoublyExponential.lean#L90

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

theorem EscapeCriterion.dist_logOrbitSeq_le_two_div(hz : escapeRadius c < ‖z‖) (n : ℕ) :
    dist (logOrbitSeq c z n) (logOrbitSeq c z (n + 1)) ≤ (2 / ‖z‖) * (1 / 2 : ℝ) ^ (n + 1) := by sorry

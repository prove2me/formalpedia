-- Prove2me | Theorems.Thm_EscapeCriterion_escapeRate_pos
-- name    : EscapeCriterion.escapeRate_pos
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:44:17.78179+00:00
-- url     : https://prove2.me/theorems/7488dcbf-726b-4327-b0ac-f8738ff6bbeb
-- title:
--   Positivity of the escape rate.
-- statement:
--   **Positivity of the escape rate.** Every escaping point has strictly positive escape
--   rate: iterate the functional equation until the orbit exceeds `3 > e`, where the a priori
--   estimate forces positivity.
--
--   ```lean
--   theorem EscapeCriterion.escapeRate_pos(hz : escapeRadius c < ‖z‖) : 0 < escapeRate c z := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EscapeRateGreenFunction.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EscapeRateGreenFunction.lean#L205

-- Thm stub generated from Novelty/EscapeRateGreenFunction.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeRateGreenFunction

/-!
# The escape rate (Green's function) of an escaping orbit

Building on the escape criterion of `Novelty.EscapeCriterionIteration`, this file constructs
the **escape rate**
`G_c(z) = lim_{n→∞} 2^{-n} · log ‖f_c^n(z)‖`
for every point `z` that has crossed the escape radius of `c`, and establishes its defining
structural properties:

* `log_distortion` / `abs_log_orbit_succ_sub`: the one-step doubling law
  `log ‖f_c(w)‖ = 2 log ‖w‖ + O(1/‖w‖)` in the escaping region, proved from the two-sided
  estimate `‖w‖² - ‖w‖ ≤ ‖f_c(w)‖ ≤ ‖w‖² + ‖w‖` and the exponential bounds
  `1 + x ≤ exp x`, `(1 + 2u)⁻¹ ≤ 1 - u` (`u ≤ 1/2`).
* `escapeRate_tendsto`: the limit exists — the increments are summable with geometric
  majorant `2^{-(n+1)}`.
* `escapeRate_functional_equation`: `G_c(f_c z) = 2 · G_c(z)`, the Böttcher/Green functional
  equation, and its iterate `escapeRate_iterate`.
* `abs_escapeRate_sub_log_le_one`: `|G_c(z) - log ‖z‖| ≤ 1`, an effective a priori estimate.
* `escapeRate_pos`: `G_c(z) > 0` for every escaping `z`, obtained by iterating the functional
  equation until the orbit exceeds `3 > e`, where the a priori estimate forces positivity.

Thus the escape-time test of `Novelty.EscapeCriterionIteration` is refined from a Boolean
test into a positive real-valued potential, and the qualitative statement "the orbit escapes"
becomes the quantitative statement `G_c(z) > 0`.
-/

open EscapeCriterion

open Filter
open scoped Topology

variable {c z : ℂ}



/-! ## Basic estimates in the escaping region -/










/-! ## The functional equation -/




/-! ## Effective bounds and positivity -/

theorem EscapeCriterion.escapeRate_pos(hz : escapeRadius c < ‖z‖) : 0 < escapeRate c z := by sorry

-- Prove2me | Definitions.Def_Novelty_EscapeRateGreenFunction
-- name    : Novelty_EscapeRateGreenFunction
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:23:13.237092+00:00
-- url     : https://prove2.me/theorems/1d102196-9bb5-400f-8520-f2c8765d8f81
-- title:
--   Aether Catalog definitions — Novelty_EscapeRateGreenFunction
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EscapeRateGreenFunction`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EscapeRateGreenFunction.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration

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

namespace EscapeCriterion

open Filter
open scoped Topology

variable {c z : ℂ}

/-- The normalised logarithmic orbit sequence whose limit is the escape rate. -/
noncomputable def logOrbitSeq (c z : ℂ) (n : ℕ) : ℝ := Real.log ‖orbit c z n‖ / 2 ^ n

/-- The escape rate (Green's function of the filled Julia set) at `z`. -/
noncomputable def escapeRate (c z : ℂ) : ℝ := limUnder Filter.atTop (logOrbitSeq c z)

/-! ## Basic estimates in the escaping region -/










/-! ## The functional equation -/




/-! ## Effective bounds and positivity -/



end EscapeCriterion



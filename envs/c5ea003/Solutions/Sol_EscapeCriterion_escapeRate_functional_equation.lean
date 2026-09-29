-- Prove2me | solution 1 for EscapeCriterion.escapeRate_functional_equation
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:28:52.726809+00:00
-- url     : https://prove2.me/submissions/5bc76572-0bce-494b-8cec-82da0e0ef7ba

-- Sol generated from Novelty/EscapeRateGreenFunction.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeRateGreenFunction
import Definitions.Def_Novelty_MandelbrotQuadraticEscape
import Theorems.Thm_EscapeCriterion_escapeRadius_lt_qmap_norm
import Theorems.Thm_EscapeCriterion_escapeRate_tendsto
import Theorems.Thm_EscapeCriterion_orbit_qmap

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




open EscapeCriterion in
theorem solution(hz : escapeRadius c < ‖z‖) :
    escapeRate c (MandelbrotEscape.qmap c z) = 2 * escapeRate c z := by
  have hz1 : escapeRadius c < ‖MandelbrotEscape.qmap c z‖ := escapeRadius_lt_qmap_norm c z hz
  have h1 : Filter.Tendsto (logOrbitSeq c (MandelbrotEscape.qmap c z)) Filter.atTop
      (𝓝 (escapeRate c (MandelbrotEscape.qmap c z))) := escapeRate_tendsto hz1
  have h2 : Filter.Tendsto (fun n => 2 * logOrbitSeq c z (n + 1)) Filter.atTop (𝓝 (2 * escapeRate c z)) :=
    Filter.Tendsto.const_mul 2
      ((Filter.tendsto_add_atTop_iff_nat (f := logOrbitSeq c z) 1).mpr (escapeRate_tendsto hz))
  have heq : ∀ n, logOrbitSeq c (MandelbrotEscape.qmap c z) n = 2 * logOrbitSeq c z (n + 1) := by
    intro n
    rw [logOrbitSeq, logOrbitSeq, orbit_qmap, pow_succ]
    field_simp
  exact tendsto_nhds_unique (Filter.Tendsto.congr heq h1) h2

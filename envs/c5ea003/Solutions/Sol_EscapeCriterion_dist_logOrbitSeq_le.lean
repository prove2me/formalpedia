-- Prove2me | solution 1 for EscapeCriterion.dist_logOrbitSeq_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:12:32.067549+00:00
-- url     : https://prove2.me/submissions/5d0b2bf1-47d5-4c93-9865-74d680b08d18

-- Sol generated from Novelty/EscapeRateGreenFunction.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeRateGreenFunction
import Theorems.Thm_EscapeCriterion_abs_log_orbit_succ_sub
import Theorems.Thm_EscapeCriterion_two_lt_norm_orbit

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
theorem solution(hz : escapeRadius c < ‖z‖) (n : ℕ) :
    dist (logOrbitSeq c z n) (logOrbitSeq c z (n + 1)) ≤ (1 / 2 : ℝ) ^ (n + 1) := by
  have hr2 : 2 < ‖orbit c z n‖ := two_lt_norm_orbit hz n
  have hkey := abs_log_orbit_succ_sub hz n
  have hbound : 2 / ‖orbit c z n‖ ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hpowpos : (0 : ℝ) < 2 ^ (n + 1) := by positivity
  rw [Real.dist_eq, logOrbitSeq, logOrbitSeq]
  have hexpand :
      Real.log ‖orbit c z n‖ / 2 ^ n - Real.log ‖orbit c z (n + 1)‖ / 2 ^ (n + 1)
        = -(Real.log ‖orbit c z (n + 1)‖ - 2 * Real.log ‖orbit c z n‖) / 2 ^ (n + 1) := by
    field_simp
    ring
  rw [hexpand, abs_div, abs_neg, abs_of_pos hpowpos, div_le_iff₀ hpowpos]
  have hone : (1 / 2 : ℝ) ^ (n + 1) * 2 ^ (n + 1) = 1 := by
    rw [div_pow, one_pow, div_mul_cancel₀]
    positivity
  rw [hone]
  exact le_trans hkey hbound

-- Prove2me | solution 1 for EscapeCriterion.log_distortion
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:09:52.109234+00:00
-- url     : https://prove2.me/submissions/fa3c2de5-b819-413f-a0a8-959ec8ac53ee

-- Sol generated from Novelty/EscapeRateGreenFunction.lean
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




open EscapeCriterion in
theorem solution(r s : ℝ) (hr : 2 < r) (hlow : r ^ 2 - r ≤ s) (hhigh : s ≤ r ^ 2 + r) :
    |Real.log s - 2 * Real.log r| ≤ 2 / r := by
  have hrpos : (0 : ℝ) < r := by linarith
  have hr2 : (0 : ℝ) < r ^ 2 := by positivity
  have hspos : 0 < s := by nlinarith
  have hexp : (1 : ℝ) + 2 / r ≤ Real.exp (2 / r) := by
    linarith [Real.add_one_le_exp (2 / r)]
  have hup : Real.log s ≤ 2 * Real.log r + 2 / r := by
    have h1 : s ≤ r ^ 2 * Real.exp (2 / r) := by
      have h2 : r ^ 2 * (1 + 2 / r) = r ^ 2 + 2 * r := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hexp hr2.le]
    calc Real.log s ≤ Real.log (r ^ 2 * Real.exp (2 / r)) := Real.log_le_log hspos h1
      _ = 2 * Real.log r + 2 / r := by
          rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
          push_cast; ring
  have hlo : 2 * Real.log r - 2 / r ≤ Real.log s := by
    have hpos1 : (0 : ℝ) < 1 + 2 / r := by positivity
    have hinv : Real.exp (-(2 / r)) ≤ 1 - 1 / r := by
      rw [Real.exp_neg]
      have h3 : (Real.exp (2 / r))⁻¹ ≤ (1 + 2 / r)⁻¹ := inv_anti₀ hpos1 hexp
      have h4 : (1 + 2 / r)⁻¹ ≤ 1 - 1 / r := by
        rw [inv_le_iff_one_le_mul₀ hpos1]
        have he : (1 - 1 / r) * (1 + 2 / r) = 1 + 1 / r - 2 / r ^ 2 := by field_simp; ring
        rw [he]
        have h6 : 2 / r ^ 2 ≤ 1 / r := by
          rw [div_le_div_iff₀ (by positivity) hrpos]; nlinarith
        linarith
      linarith
    have h1 : r ^ 2 * Real.exp (-(2 / r)) ≤ s := by
      have h5 : r ^ 2 * (1 - 1 / r) = r ^ 2 - r := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hinv hr2.le]
    calc 2 * Real.log r - 2 / r = Real.log (r ^ 2 * Real.exp (-(2 / r))) := by
          rw [Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_pow, Real.log_exp]
          push_cast; ring
      _ ≤ Real.log s := Real.log_le_log (by positivity) h1
  rw [abs_le]
  constructor <;> linarith

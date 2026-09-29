-- Prove2me | solution 1 for EscapeCriterion.continuousOn_mandelbrotPotential
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:26:26.791337+00:00
-- url     : https://prove2.me/submissions/fac4aff3-9356-4e51-9252-ca6fa810d127

-- Sol generated from Novelty/EscapeRateContinuity.lean
import Mathlib
import Definitions.Def_Novelty_EscapeDoublyExponential
import Definitions.Def_Novelty_EscapeRateContinuity
import Definitions.Def_Novelty_FilledJuliaCompact
import Theorems.Thm_EscapeCriterion_abs_potentialSeq_sub_le
import Theorems.Thm_EscapeCriterion_continuousOn_potentialSeq

/-!
# Uniform convergence and continuity of the escape rate

Fifth iteration of the escape-criterion thread. The increment bound
`dist_logOrbitSeq_le` is *uniform* in both the point `z` and the parameter `c`: the
`n`-th term of the defining sequence of the escape rate differs from its limit by at most
`2^{-n}`, whatever escaping `z` and whatever `c`. Consequently the convergence is uniform
on the whole escaping region, and the escape rate inherits continuity from the polynomial
iterates.

Main results:

* `abs_logOrbitSeq_sub_escapeRate_le`: `|2^{-n} log ‖z_n‖ - G_c(z)| ≤ 2^{-n}`, an explicit
  error bound for the numerical computation of the escape rate.
* `tendstoUniformlyOn_logOrbitSeq`: uniform convergence on the escaping region.
* `continuousOn_escapeRate`: `G_c` is continuous on `{z | ‖z‖ > max 2 ‖c‖}`.
* `continuousOn_mandelbrotPotential`: the Douady–Hubbard potential `G_M` is continuous on
  `{c | ‖c‖ > 2}`, obtained from the same uniform estimate in the *parameter*.
-/

open EscapeCriterion

open Filter MandelbrotEscape
open scoped Topology

variable {c z : ℂ}





/-! ## Continuity of the Douady–Hubbard potential -/







open EscapeCriterion in
theorem solution:
    ContinuousOn mandelbrotPotential {c : ℂ | 2 < ‖c‖} := by
  have huniform : TendstoUniformlyOn potentialSeq mandelbrotPotential Filter.atTop {c : ℂ | 2 < ‖c‖} := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ : ∃ N : ℕ, (1 / 2 : ℝ) ^ N < ε :=
      exists_pow_lt_of_lt_one hε (by norm_num)
    filter_upwards [eventually_ge_atTop N] with n hn c hc
    have hbound := abs_potentialSeq_sub_le hc n
    have hmono : (1 / 2 : ℝ) ^ n ≤ (1 / 2 : ℝ) ^ N :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
    rw [Real.dist_eq, abs_sub_comm]
    linarith
  exact huniform.continuousOn ((Eventually.of_forall continuousOn_potentialSeq).frequently)

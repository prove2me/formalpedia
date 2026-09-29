-- Prove2me | solution 1 for EscapeCriterion.abs_potentialSeq_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:19:15.641918+00:00
-- url     : https://prove2.me/submissions/12efcc8c-34ce-494f-b50e-2978787856e1

-- Sol generated from Novelty/EscapeRateContinuity.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeDoublyExponential
import Definitions.Def_Novelty_EscapeRateContinuity
import Definitions.Def_Novelty_EscapeRateGreenFunction
import Definitions.Def_Novelty_FilledJuliaCompact
import Theorems.Thm_EscapeCriterion_abs_logOrbitSeq_sub_escapeRate_le
import Theorems.Thm_EscapeCriterion_escapeRadius_lt_norm_critOrbit_two

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
theorem solution(hc : 2 < ‖c‖) (n : ℕ) :
    |potentialSeq n c - mandelbrotPotential c| ≤ (1 / 2 : ℝ) ^ n := by
  have hz2 : escapeRadius c < ‖orbit c 0 2‖ := escapeRadius_lt_norm_critOrbit_two hc
  have h := abs_logOrbitSeq_sub_escapeRate_le hz2 n
  have hhalf : |potentialSeq n c - mandelbrotPotential c|
      = |logOrbitSeq c (orbit c 0 2) n - escapeRate c (orbit c 0 2)| / 2 := by
    rw [potentialSeq, mandelbrotPotential, ← abs_of_pos (show (0:ℝ) < 2 by norm_num),
      ← abs_div]
    congr 1
    ring
  rw [hhalf]
  have hpos : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  linarith [abs_nonneg (logOrbitSeq c (orbit c 0 2) n - escapeRate c (orbit c 0 2))]

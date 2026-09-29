-- Prove2me | solution 1 for EscapeCriterion.abs_logOrbitSeq_sub_escapeRate_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:17:44.798031+00:00
-- url     : https://prove2.me/submissions/87fff4f0-bdcd-41c9-841d-79421c5f47aa

-- Sol generated from Novelty/EscapeRateContinuity.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeRateContinuity
import Definitions.Def_Novelty_EscapeRateGreenFunction
import Definitions.Def_Novelty_FilledJuliaCompact
import Theorems.Thm_EscapeCriterion_dist_logOrbitSeq_le
import Theorems.Thm_EscapeCriterion_escapeRate_tendsto
import Theorems.Thm_EscapeCriterion_summable_geom_half

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
theorem solution(hz : escapeRadius c < ‖z‖) (n : ℕ) :
    |logOrbitSeq c z n - escapeRate c z| ≤ (1 / 2 : ℝ) ^ n := by
  have hdist := dist_le_tsum_of_dist_le_of_tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ (k + 1))
    (fun k => dist_logOrbitSeq_le hz k) summable_geom_half (escapeRate_tendsto hz) n
  have htsum : (∑' m : ℕ, (1 / 2 : ℝ) ^ (n + m + 1)) = (1 / 2 : ℝ) ^ n := by
    have h : ∀ m : ℕ, (1 / 2 : ℝ) ^ (n + m + 1) = ((1 / 2 : ℝ) ^ (n + 1)) * (1 / 2 : ℝ) ^ m := by
      intro m
      rw [← pow_add]
      ring_nf
    rw [tsum_congr h, tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    rw [pow_succ]
    ring
  rw [htsum] at hdist
  rwa [Real.dist_eq] at hdist

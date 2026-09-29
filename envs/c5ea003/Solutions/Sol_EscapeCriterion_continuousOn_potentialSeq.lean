-- Prove2me | solution 1 for EscapeCriterion.continuousOn_potentialSeq
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:25:06.649579+00:00
-- url     : https://prove2.me/submissions/d370fae3-f3d3-41cb-b1ae-ae5ca61f54c6

-- Sol generated from Novelty/EscapeRateContinuity.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeRateContinuity
import Definitions.Def_Novelty_EscapeRateGreenFunction
import Definitions.Def_Novelty_FilledJuliaCompact
import Definitions.Def_Novelty_MandelbrotQuadraticEscape
import Theorems.Thm_EscapeCriterion_continuous_critOrbit
import Theorems.Thm_EscapeCriterion_critOrbit_eq_orbit
import Theorems.Thm_EscapeCriterion_escapeRadius_lt_norm_critOrbit_two
import Theorems.Thm_EscapeCriterion_orbit_add
import Theorems.Thm_EscapeCriterion_two_lt_norm_orbit

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


lemma potentialSeq_eq (n : ℕ) (c : ℂ) :
    potentialSeq n c = Real.log ‖critOrbit c (n + 2)‖ / 2 ^ (n + 1) := by
  rw [potentialSeq, logOrbitSeq, critOrbit_eq_orbit, ← orbit_add, Nat.add_comm 2 n, pow_succ]
  field_simp





open EscapeCriterion in
theorem solution(n : ℕ) :
    ContinuousOn (potentialSeq n) {c : ℂ | 2 < ‖c‖} := by
  intro c hc
  refine ContinuousAt.continuousWithinAt ?_
  have hne : ‖critOrbit c (n + 2)‖ ≠ 0 := by
    have hz2 : escapeRadius c < ‖orbit c 0 2‖ := escapeRadius_lt_norm_critOrbit_two hc
    have h2 : 2 < ‖orbit c (orbit c 0 2) n‖ := two_lt_norm_orbit hz2 n
    have hidx : orbit c (orbit c 0 2) n = critOrbit c (n + 2) := by
      rw [critOrbit_eq_orbit, ← orbit_add, Nat.add_comm 2 n]
    rw [hidx] at h2
    positivity
  have hcont : ContinuousAt (fun c : ℂ => Real.log ‖critOrbit c (n + 2)‖ / 2 ^ (n + 1)) c :=
    ContinuousAt.div_const
      (ContinuousAt.log ((continuous_critOrbit (n + 2)).norm).continuousAt hne) _
  exact hcont.congr (Filter.Eventually.of_forall fun c => (potentialSeq_eq n c).symm)

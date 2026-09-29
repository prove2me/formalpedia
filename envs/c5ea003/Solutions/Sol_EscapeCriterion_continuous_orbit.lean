-- Prove2me | solution 1 for EscapeCriterion.continuous_orbit
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:26:27.612089+00:00
-- url     : https://prove2.me/submissions/694b97da-0842-4ad7-bc29-bb07fc35795e

-- Sol generated from Novelty/FilledJuliaCompact.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeDoublyExponential
import Definitions.Def_Novelty_FilledJuliaCompact
import Theorems.Thm_EscapeCriterion_orbit_succ

/-!
# The filled Julia set as the exact complement of the escape-time test

Fourth iteration of the escape-criterion thread. The escape-time test
(`EscapeCriterion.bounded_iff_never_escapes`) says that an orbit is bounded iff it never
leaves the disk of radius `escapeRadius c`. Here that equivalence is used to give the
filled Julia set
`K_c = {z | the orbit of z under f_c is bounded}`
its standard structure theory, entirely from the escape estimates:

* `mem_filledJulia_iff`: membership is decided by the radius-`max 2 ‖c‖` test.
* `filledJulia_qmap_iff`: total invariance `z ∈ K_c ↔ f_c z ∈ K_c`.
* `isClosed_filledJulia`, `isCompact_filledJulia`: `K_c` is compact.
* `filledJulia_nonempty`: `K_c` is nonempty — via the algebraic input that `z² - z + c` has a
  root in `ℂ`, i.e. a fixed point of `f_c`, whose orbit is constant.
* `filledJulia_eq_iInter`: `K_c` is the nested intersection of the escape-time test sets,
  the dynamical counterpart of `Mandelbrot_eq_iInter`.
* `escapeRate_pos_of_not_mem`: outside `K_c` the escape rate is strictly positive, so
  `K_c = {z | G_c(z) = 0}` on the region where `G_c` is defined (`filledJulia_eq_zero_set`).
-/

open EscapeCriterion

open Filter MandelbrotEscape
open scoped Topology

variable {c z : ℂ}
















open EscapeCriterion in
theorem solution(c : ℂ) (n : ℕ) : Continuous fun z : ℂ => orbit c z n := by
  induction n with
  | zero => simpa using continuous_id
  | succ n ih =>
    simp only [orbit_succ]
    exact (ih.pow 2).add continuous_const

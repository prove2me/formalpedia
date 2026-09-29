-- Prove2me | solution 1 for EscapeCriterion.filledJulia_qmap_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:31:55.611164+00:00
-- url     : https://prove2.me/submissions/a1a6cf02-ec00-46f0-b6b0-e8a8e7b37190

-- Sol generated from Novelty/FilledJuliaCompact.lean
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeDoublyExponential
import Definitions.Def_Novelty_FilledJuliaCompact
import Definitions.Def_Novelty_MandelbrotQuadraticEscape
import Theorems.Thm_EscapeCriterion_bounded_iff_never_escapes
import Theorems.Thm_EscapeCriterion_orbit_qmap
import Theorems.Thm_EscapeCriterion_tendsto_atTop_of_exists_escape

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


theorem mem_filledJulia_iff (c z : ℂ) :
    z ∈ filledJulia c ↔ ∀ n, ‖orbit c z n‖ ≤ escapeRadius c :=
  bounded_iff_never_escapes c z














open EscapeCriterion in
theorem solution(c z : ℂ) : z ∈ filledJulia c ↔ qmap c z ∈ filledJulia c := by
  constructor
  · rintro ⟨B, hB⟩
    refine ⟨B, fun n => ?_⟩
    rw [orbit_qmap]
    exact hB (n + 1)
  · intro h
    rw [mem_filledJulia_iff]
    intro n
    by_contra hlt
    push_neg at hlt
    have hdiv := tendsto_atTop_of_exists_escape c z ⟨n, hlt⟩
    obtain ⟨B, hB⟩ := h
    have hdiv' : Filter.Tendsto (fun k => ‖orbit c (qmap c z) k‖) Filter.atTop Filter.atTop := by
      rw [← Filter.tendsto_add_atTop_iff_nat 1] at hdiv
      exact hdiv.congr fun k => by rw [orbit_qmap, Nat.add_comm]
    obtain ⟨m, hm⟩ := (hdiv'.eventually_gt_atTop B).exists
    exact absurd (hB m) (not_le.mpr hm)

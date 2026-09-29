-- Prove2me | Definitions.Def_Novelty_FilledJuliaCompact
-- name    : Novelty_FilledJuliaCompact
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:24:34.538474+00:00
-- url     : https://prove2.me/theorems/7d33c401-65f5-4cc9-a40f-e8f8e867f297
-- title:
--   Aether Catalog definitions — Novelty_FilledJuliaCompact
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.FilledJuliaCompact`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/FilledJuliaCompact.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_EscapeCriterionIteration
import Definitions.Def_Novelty_EscapeDoublyExponential

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

namespace EscapeCriterion

open Filter MandelbrotEscape
open scoped Topology

variable {c z : ℂ}

/-- The filled Julia set of `f_c`: the points with bounded forward orbit. -/
def filledJulia (c : ℂ) : Set ℂ := {z | BoundedOrbit c z}




/-- The escape-time test sets for the point-dynamics. -/
def juliaTestSet (c : ℂ) (n : ℕ) : Set ℂ := {z | ∀ k ≤ n, ‖orbit c z k‖ ≤ escapeRadius c}










end EscapeCriterion



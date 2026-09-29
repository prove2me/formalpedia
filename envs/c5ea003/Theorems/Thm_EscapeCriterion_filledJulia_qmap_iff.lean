-- Prove2me | Theorems.Thm_EscapeCriterion_filledJulia_qmap_iff
-- name    : EscapeCriterion.filledJulia_qmap_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:44:28.569801+00:00
-- url     : https://prove2.me/theorems/2523da91-86ad-4d7b-b4a8-491095aaebe5
-- title:
--   Total invariance: `z` has bounded orbit iff `f_c z` does.
-- statement:
--   **Total invariance**: `z` has bounded orbit iff `f_c z` does.
--
--   ```lean
--   theorem EscapeCriterion.filledJulia_qmap_iff(c z : ℂ) : z ∈ filledJulia c ↔ qmap c z ∈ filledJulia c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/FilledJuliaCompact.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/FilledJuliaCompact.lean#L43

-- Thm stub generated from Novelty/FilledJuliaCompact.lean
import Mathlib
import Definitions.Def_Novelty_EscapeDoublyExponential
import Definitions.Def_Novelty_FilledJuliaCompact
import Definitions.Def_Novelty_MandelbrotQuadraticEscape

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

theorem EscapeCriterion.filledJulia_qmap_iff(c z : ℂ) : z ∈ filledJulia c ↔ qmap c z ∈ filledJulia c := by sorry

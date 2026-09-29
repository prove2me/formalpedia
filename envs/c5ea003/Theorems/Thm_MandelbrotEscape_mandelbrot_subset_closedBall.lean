-- Prove2me | Theorems.Thm_MandelbrotEscape_mandelbrot_subset_closedBall
-- name    : MandelbrotEscape.mandelbrot_subset_closedBall
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:07:10.410235+00:00
-- url     : https://prove2.me/theorems/e1a70ab5-f95a-4f71-8b8a-b10d5b74c139
-- title:
--   Mandelbrot subset closedBall
-- statement:
--   Formal statement of `MandelbrotEscape.mandelbrot_subset_closedBall` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem MandelbrotEscape.mandelbrot_subset_closedBall{c : ℂ} (hc : c ∈ Mandelbrot) : ‖c‖ ≤ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/MandelbrotQuadraticEscape.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/MandelbrotQuadraticEscape.lean#L75

-- Thm stub generated from Novelty/MandelbrotQuadraticEscape.lean
import Mathlib
import Definitions.Def_Novelty_MandelbrotQuadraticEscape

/-!
# The Mandelbrot Set: Quadratic Recurrence and the Escape Radius

The Mandelbrot set `M` is the set of complex parameters `c` for which the *critical orbit*
`0, c, c²+c, …` of the quadratic map `f_c(z) = z² + c` stays bounded.

This file develops the elementary — but genuinely quantitative — dynamics of the recurrence
`z_{n+1} = z_n² + c` and proves the classical **escape-radius theorem**: if `‖c‖ > 2` then the
critical orbit diverges to infinity, so `M` is contained in the closed disk of radius `2`.

The heart of the argument is a geometric lower bound on the orbit:
`‖c‖·(‖c‖-1)ⁿ ≤ ‖f_c^{(n+1)}(0)‖`, which forces divergence because `‖c‖ - 1 > 1`.

We also record two concrete membership facts: `0 ∈ M` and `-1 ∈ M` (the orbit of `-1` is the
`2`-cycle `0, -1, 0, -1, …`), while every `c` with `‖c‖ > 2` lies outside `M`.
-/

open MandelbrotEscape

open Filter
open scoped Topology






/-
Reverse triangle inequality specialised to the quadratic map:
`‖z‖² - ‖c‖ ≤ ‖z² + c‖`.
-/

/-
The key growth invariant.  If `‖c‖ > 2`, then for every `n` the `(n+1)`-st iterate of the
critical orbit is at least `‖c‖` in norm, and in fact grows geometrically at rate `‖c‖ - 1`.
-/

/-
**Escape theorem.**  If `‖c‖ > 2`, the norm of the critical orbit tends to infinity.
-/

/-
**Escape radius / a-priori bound for the Mandelbrot set.**
Every parameter in the Mandelbrot set has norm at most `2`.
-/

theorem MandelbrotEscape.mandelbrot_subset_closedBall{c : ℂ} (hc : c ∈ Mandelbrot) : ‖c‖ ≤ 2 := by sorry

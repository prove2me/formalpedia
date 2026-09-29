-- Prove2me | Theorems.Thm_MandelbrotEscape_critOrbit_succ
-- name    : MandelbrotEscape.critOrbit_succ
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:43:06.37813+00:00
-- url     : https://prove2.me/theorems/c76ecac9-8734-4b0e-abfa-baf36bdb2639
-- title:
--   CritOrbit succ
-- statement:
--   Formal statement of `MandelbrotEscape.critOrbit_succ` from the Aether Catalog (Novelty). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem MandelbrotEscape.critOrbit_succ(c : ℂ) (n : ℕ) :
--       critOrbit c (n + 1) = (critOrbit c n) ^ 2 + c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/MandelbrotQuadraticEscape.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/MandelbrotQuadraticEscape.lean#L35

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

theorem MandelbrotEscape.critOrbit_succ(c : ℂ) (n : ℕ) :
    critOrbit c (n + 1) = (critOrbit c n) ^ 2 + c := by sorry

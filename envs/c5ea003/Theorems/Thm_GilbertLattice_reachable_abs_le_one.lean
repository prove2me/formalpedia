-- Prove2me | Theorems.Thm_GilbertLattice_reachable_abs_le_one
-- name    : GilbertLattice.reachable_abs_le_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:35:37.698705+00:00
-- url     : https://prove2.me/theorems/16ef4add-8dc5-4b68-9bee-08c900b4d665
-- title:
--   Main lower bound.
-- statement:
--   **Main lower bound.**  If `R < 1/3` then, for every placement of the points, every
--   cell reachable from `c` differs from `c` by at most one in each coordinate.
--
--   ```lean
--   theorem GilbertLattice.reachable_abs_le_one(hR : R < 1 / 3) {c d : ℤ × ℤ}
--       (h : (gilbert R C).Reachable c d) : |d.1 - c.1| ≤ 1 ∧ |d.2 - c.2| ≤ 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GilbertLatticeLowerBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GilbertLatticeLowerBound.lean#L352

-- Thm stub generated from Shared/GilbertLatticeLowerBound.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeLowerBound

/-!
# No percolation below the radius `1/3`, for any placement of the points

This file proves a *deterministic* lower bound for the geometric critical radius of the
conditioned Gilbert model: if `R < 1/3` then, whatever the placement of the points, all
connected components of the Gilbert graph are contained in a `3 × 3` block of cells; in
particular every connected component is finite and no placement percolates.

## The argument

Write `p_c = (px c, py c)` for the point of the cell `c`.

*Crossing lemma.*  If an edge joins two cells with different first coordinates, then the
two points lie on either side of the vertical line `x = K` separating the two columns,
at distance `< R` from it (`GilbertLattice.cross_x`); similarly for rows
(`GilbertLattice.cross_y`).

*Uniqueness of the crossed line.*  Two integers at distance `< 3R < 1` are equal.  Hence
all the vertical lines crossed along a path are the same one, provided the current point
stays within `2R` of the previously crossed line.

*The invariant.*  Along a path with previous cell `prev` and current cell `c` we
maintain (`GilbertLattice.Inv`): the columns of `prev` and `c` are among `{K-1, K}`, the
rows among `{J-1, J}`, the abscissa of the current point is within `2R` of `K` — and
even within `R` of `K` if the last step changed the column — and symmetrically for the
ordinate.  The invariant propagates along an edge as soon as the new cell differs from
`prev` (`GilbertLattice.inv_step`): a step which does not change the column can only
increase the slack in `x` from `R` to `2R`, and a step which changes neither the slack
in `x` nor the slack in `y` would force the walk to come back to `prev`.

Since a path enters the invariant after at most two steps
(`GilbertLattice.inv_start`), every cell reachable from `c` differs from `c` by at most
one in each coordinate (`GilbertLattice.reachable_abs_le_one`), components are finite
(`GilbertLattice.component_finite`) and no configuration percolates
(`GilbertLattice.not_infinite_component`).
-/

open GilbertLattice

variable {R : ℝ} {C : Config}

theorem GilbertLattice.reachable_abs_le_one(hR : R < 1 / 3) {c d : ℤ × ℤ}
    (h : (gilbert R C).Reachable c d) : |d.1 - c.1| ≤ 1 ∧ |d.2 - c.2| ≤ 1 := by sorry

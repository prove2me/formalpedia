-- Prove2me | Theorems.Thm_GilbertLattice_cross_x
-- name    : GilbertLattice.cross_x
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:24:16.166441+00:00
-- url     : https://prove2.me/theorems/7e3e97b3-d5a1-47fb-b1b3-673835d7c7e2
-- title:
--   Cross x
-- statement:
--   Formal statement of `GilbertLattice.cross_x` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem GilbertLattice.cross_x(hR : R < 1) {c c' : ℤ × ℤ} (hadj : (gilbert R C).Adj c c')
--       (hne : c.1 ≠ c'.1) :
--       ∃ K : ℤ, (c.1 = K ∨ c.1 = K - 1) ∧ (c'.1 = K ∨ c'.1 = K - 1) ∧
--         |px C c - (K : ℝ)| < R ∧ |px C c' - (K : ℝ)| < R := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GilbertLatticeLowerBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GilbertLatticeLowerBound.lean#L63

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

theorem GilbertLattice.cross_x(hR : R < 1) {c c' : ℤ × ℤ} (hadj : (gilbert R C).Adj c c')
    (hne : c.1 ≠ c'.1) :
    ∃ K : ℤ, (c.1 = K ∨ c.1 = K - 1) ∧ (c'.1 = K ∨ c'.1 = K - 1) ∧
      |px C c - (K : ℝ)| < R ∧ |px C c' - (K : ℝ)| < R := by sorry

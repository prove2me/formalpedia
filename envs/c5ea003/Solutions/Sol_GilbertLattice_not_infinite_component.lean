-- Prove2me | solution 1 for GilbertLattice.not_infinite_component
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:26:13.867572+00:00
-- url     : https://prove2.me/submissions/f97a50fb-6fa5-48ce-af93-e1940cb05f1e

-- Sol generated from Shared/GilbertLatticeLowerBound.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeLowerBound
import Theorems.Thm_GilbertLattice_reachable_abs_le_one

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













/-- For `R < 1/3` every connected component of the Gilbert graph is finite (it is
contained in a `3 × 3` block of cells). -/
theorem component_finite (hR : R < 1 / 3) (c : ℤ × ℤ) :
    {d : ℤ × ℤ | (gilbert R C).Reachable c d}.Finite := by
  apply Set.Finite.subset (Set.finite_Icc (c.1 - 1, c.2 - 1) (c.1 + 1, c.2 + 1))
  intro d hd
  obtain ⟨h1, h2⟩ := reachable_abs_le_one hR hd
  rw [abs_le] at h1 h2
  rw [Set.mem_Icc, Prod.le_def, Prod.le_def]
  exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩



open GilbertLattice in
theorem solution(hR : R < 1 / 3) (c : ℤ × ℤ) :
    ¬ {d : ℤ × ℤ | (gilbert R C).Reachable c d}.Infinite :=
  fun h => h (component_finite hR c)

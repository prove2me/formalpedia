-- Prove2me | solution 1 for GilbertLattice.inv_walk
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:23:21.560416+00:00
-- url     : https://prove2.me/submissions/c35f5433-3d94-459c-98fd-2d167a149e80

-- Sol generated from Shared/GilbertLatticeLowerBound.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeLowerBound
import Theorems.Thm_GilbertLattice_inv_step

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
















open GilbertLattice in
lemma solution(hR : R < 1 / 3) (hR0 : 0 < R) {K J : ℤ} {c d : ℤ × ℤ}
    (w : (gilbert R C).Walk c d) :
    ∀ {prev : ℤ × ℤ}, Inv R C K J prev c → w.IsPath → prev ∉ w.support →
      ∀ e ∈ w.support, (e.1 = K ∨ e.1 = K - 1) ∧ (e.2 = J ∨ e.2 = J - 1) := by
  induction w with
  | nil =>
      intro prev hinv _ _ e he
      simp only [SimpleGraph.Walk.support_nil, List.mem_singleton] at he
      subst he
      exact ⟨hinv.col, hinv.row⟩
  | @cons u v z hadj w ih =>
      intro prev hinv hpath hprev e he
      rw [SimpleGraph.Walk.support_cons, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨hinv.col, hinv.row⟩
      · rw [SimpleGraph.Walk.cons_isPath_iff] at hpath
        rw [SimpleGraph.Walk.support_cons, List.mem_cons] at hprev
        push_neg at hprev
        have hne' : v ≠ prev := by
          intro hcon
          exact hprev.2 (hcon ▸ SimpleGraph.Walk.start_mem_support w)
        exact ih (inv_step hR hR0 hinv hadj hne') hpath.1 hpath.2 e he

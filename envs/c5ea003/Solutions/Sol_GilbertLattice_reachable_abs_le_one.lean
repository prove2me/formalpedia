-- Prove2me | solution 1 for GilbertLattice.reachable_abs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:24:52.286136+00:00
-- url     : https://prove2.me/submissions/256b5319-9995-4ed0-ae68-d6a422c6bb99

-- Sol generated from Shared/GilbertLatticeLowerBound.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeLowerBound
import Theorems.Thm_GilbertLattice_abs_col_le_one
import Theorems.Thm_GilbertLattice_abs_row_le_one
import Theorems.Thm_GilbertLattice_inv_start
import Theorems.Thm_GilbertLattice_inv_walk
import Theorems.Thm_GilbertLattice_radius_pos_of_adj

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
theorem solution(hR : R < 1 / 3) {c d : ℤ × ℤ}
    (h : (gilbert R C).Reachable c d) : |d.1 - c.1| ≤ 1 ∧ |d.2 - c.2| ≤ 1 := by
  rcases le_or_gt R 0 with hR0 | hR0
  · obtain ⟨w⟩ := h
    cases w with
    | nil => simp
    | cons hadj w => exact absurd (radius_pos_of_adj hadj) (not_lt.2 hR0)
  · obtain ⟨w⟩ := h
    obtain ⟨p, hp⟩ : ∃ p : (gilbert R C).Walk c d, p.IsPath := ⟨w.toPath.1, w.toPath.2⟩
    clear w
    match p, hp with
    | SimpleGraph.Walk.nil, _ => simp
    | SimpleGraph.Walk.cons hadj SimpleGraph.Walk.nil, hp =>
        exact ⟨abs_col_le_one (by linarith) hadj, abs_row_le_one (by linarith) hadj⟩
    | SimpleGraph.Walk.cons (v := c₁) hadj (SimpleGraph.Walk.cons (v := c₂) hadj₂ p₂), hp =>
        have hp1 : (SimpleGraph.Walk.cons hadj₂ p₂).IsPath := hp.of_cons
        have hnec : c₂ ≠ c := by
          intro hcon
          rw [SimpleGraph.Walk.cons_isPath_iff] at hp
          apply hp.2
          rw [SimpleGraph.Walk.support_cons, ← hcon]
          exact List.mem_cons_of_mem _ (SimpleGraph.Walk.start_mem_support p₂)
        obtain ⟨K, J, hinv, hK, hJ⟩ := inv_start hR hR0 hadj hadj₂ hnec
        have hprev : c₁ ∉ p₂.support := by
          rw [SimpleGraph.Walk.cons_isPath_iff] at hp1
          exact hp1.2
        have hd := inv_walk hR hR0 p₂ hinv (hp1.of_cons) hprev d
          (SimpleGraph.Walk.end_mem_support p₂)
        refine ⟨?_, ?_⟩
        · rw [abs_le]
          rcases hd.1 with a | a <;> rcases hK with b | b <;> omega
        · rw [abs_le]
          rcases hd.2 with a | a <;> rcases hJ with b | b <;> omega

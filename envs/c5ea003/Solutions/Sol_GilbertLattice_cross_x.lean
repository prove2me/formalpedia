-- Prove2me | solution 1 for GilbertLattice.cross_x
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:17:09.710906+00:00
-- url     : https://prove2.me/submissions/1d111dc0-8202-4786-a1a4-655d48012ad8

-- Sol generated from Shared/GilbertLatticeLowerBound.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeLowerBound
import Theorems.Thm_GilbertLattice_abs_col_le_one
import Theorems.Thm_GilbertLattice_abs_dx_lt

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


/-- The point of a cell lies in the closed cell. -/
lemma px_bounds (C : Config) (c : ℤ × ℤ) : (c.1 : ℝ) ≤ px C c ∧ px C c ≤ (c.1 : ℝ) + 1 :=
  ⟨by have := C.off_nonneg_fst c; unfold px; linarith,
   by have := C.off_le_one_fst c; unfold px; linarith⟩














open GilbertLattice in
lemma solution(hR : R < 1) {c c' : ℤ × ℤ} (hadj : (gilbert R C).Adj c c')
    (hne : c.1 ≠ c'.1) :
    ∃ K : ℤ, (c.1 = K ∨ c.1 = K - 1) ∧ (c'.1 = K ∨ c'.1 = K - 1) ∧
      |px C c - (K : ℝ)| < R ∧ |px C c' - (K : ℝ)| < R := by
  have hd := abs_dx_lt hadj
  have hle := abs_col_le_one hR.le hadj
  rw [abs_le] at hle
  have hb := px_bounds C c
  have hb' := px_bounds C c'
  rw [abs_lt] at hd
  rcases (show c'.1 = c.1 + 1 ∨ c'.1 = c.1 - 1 by omega) with h1 | h1
  · refine ⟨c.1 + 1, Or.inr (by omega), Or.inl (by omega), ?_, ?_⟩
    · have e : ((c'.1 : ℤ) : ℝ) = (c.1 : ℝ) + 1 := by rw [h1]; push_cast; ring
      push_cast
      rw [abs_lt]
      constructor <;> [linarith [hb.2, hd.1, hd.2]; linarith [hb'.1, hd.1, hd.2, e]]
    · have e : ((c'.1 : ℤ) : ℝ) = (c.1 : ℝ) + 1 := by rw [h1]; push_cast; ring
      push_cast
      rw [abs_lt]
      constructor <;> [linarith [hb'.1, hd.1, hd.2, e]; linarith [hb.2, hd.1, hd.2]]
  · refine ⟨c.1, Or.inl rfl, Or.inr (by omega), ?_, ?_⟩
    · have e : ((c'.1 : ℤ) : ℝ) = (c.1 : ℝ) - 1 := by rw [h1]; push_cast; ring
      rw [abs_lt]
      constructor <;> [linarith [hb'.2, hd.1, hd.2, e]; linarith [hb.1, hd.1, hd.2]]
    · have e : ((c'.1 : ℤ) : ℝ) = (c.1 : ℝ) - 1 := by rw [h1]; push_cast; ring
      rw [abs_lt]
      constructor <;> [linarith [hb'.2, hd.1, hd.2, e]; linarith [hb.1, hd.1, hd.2]]

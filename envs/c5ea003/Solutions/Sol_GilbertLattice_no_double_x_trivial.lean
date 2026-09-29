-- Prove2me | solution 1 for GilbertLattice.no_double_x_trivial
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:19:43.238315+00:00
-- url     : https://prove2.me/submissions/cb7572d8-b202-4d22-b06e-1e8c63d443ed

-- Sol generated from Shared/GilbertLatticeLowerBound.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeLowerBound
import Theorems.Thm_GilbertLattice_cross_y

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

/-- Two integers whose distance is `< 1` are equal. -/
lemma int_eq_of_abs_sub_lt_one {K K' : ℤ} (h : |(K : ℝ) - (K' : ℝ)| < 1) : K = K' := by
  by_contra hne
  have h1 : 1 ≤ |K - K'| := Int.one_le_abs (sub_ne_zero_of_ne hne)
  have h2 : ((1 : ℤ) : ℝ) ≤ ((|K - K'| : ℤ) : ℝ) := by exact_mod_cast h1
  rw [Int.cast_abs] at h2
  push_cast at h2
  linarith















open GilbertLattice in
lemma solution(hR : R < 1 / 3) (hR0 : 0 < R) {c₀ c₁ c₂ : ℤ × ℤ}
    (h1 : (gilbert R C).Adj c₀ c₁) (h2 : (gilbert R C).Adj c₁ c₂) (hne : c₂ ≠ c₀)
    (hx1 : c₁.1 = c₀.1) (hx2 : c₂.1 = c₁.1) : False := by
  have hR1 : R < 1 := by linarith
  have hy1 : c₀.2 ≠ c₁.2 := by
    intro hcon; exact h1.ne (Prod.ext hx1.symm hcon)
  have hy2 : c₁.2 ≠ c₂.2 := by
    intro hcon; exact h2.ne (Prod.ext hx2.symm hcon)
  obtain ⟨J₁, hJ11, hJ12, hJ13, hJ14⟩ := cross_y hR1 h1 hy1
  obtain ⟨J₂, hJ21, hJ22, hJ23, hJ24⟩ := cross_y hR1 h2 hy2
  have hJJ : J₁ = J₂ := by
    refine int_eq_of_abs_sub_lt_one ?_
    have hb : |((J₁ : ℝ)) - (J₂ : ℝ)| ≤ |(J₁ : ℝ) - py C c₁| + |py C c₁ - (J₂ : ℝ)| :=
      abs_sub_le _ _ _
    rw [abs_sub_comm ((J₁ : ℝ)) (py C c₁)] at hb
    linarith
  subst hJJ
  have : c₂.2 = c₀.2 := by
    rcases hJ12 with a | a <;> rcases hJ11 with b | b <;> rcases hJ22 with d | d <;> omega
  exact hne (Prod.ext (by omega) this)

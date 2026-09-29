-- Prove2me | solution 1 for GilbertLattice.inv_step
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:21:41.328852+00:00
-- url     : https://prove2.me/submissions/2589fe22-7d04-4691-82b4-230c246f1a74

-- Sol generated from Shared/GilbertLatticeLowerBound.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeLowerBound
import Theorems.Thm_GilbertLattice_abs_dx_lt
import Theorems.Thm_GilbertLattice_abs_dy_lt
import Theorems.Thm_GilbertLattice_cross_x
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
lemma solution(hR : R < 1 / 3) (hR0 : 0 < R) {K J : ℤ} {prev c c' : ℤ × ℤ}
    (h : Inv R C K J prev c) (hadj : (gilbert R C).Adj c c') (hne : c' ≠ prev) :
    Inv R C K J c c' := by
  have hR1 : R < 1 := by linarith
  have hdx := abs_dx_lt hadj
  have hdy := abs_dy_lt hadj
  have hcc' : c ≠ c' := hadj.ne
  -- uniqueness of the crossed lines
  have hKu : ∀ K' : ℤ, |px C c - (K' : ℝ)| < R → K' = K := by
    intro K' hK'
    refine (int_eq_of_abs_sub_lt_one ?_)
    have h1 : |((K' : ℝ)) - (K : ℝ)| ≤ |(K' : ℝ) - px C c| + |px C c - (K : ℝ)| :=
      abs_sub_le _ _ _
    rw [abs_sub_comm ((K' : ℝ)) (px C c)] at h1
    have := h.looseX
    linarith
  have hJu : ∀ J' : ℤ, |py C c - (J' : ℝ)| < R → J' = J := by
    intro J' hJ'
    refine (int_eq_of_abs_sub_lt_one ?_)
    have h1 : |((J' : ℝ)) - (J : ℝ)| ≤ |(J' : ℝ) - py C c| + |py C c - (J : ℝ)| :=
      abs_sub_le _ _ _
    rw [abs_sub_comm ((J' : ℝ)) (py C c)] at h1
    have := h.looseY
    linarith
  by_cases hx : c'.1 = c.1
  · by_cases hy : c'.2 = c.2
    · exact absurd (Prod.ext hx hy) (Ne.symm hcc')
    · -- the step crosses a horizontal line only
      obtain ⟨J', hJ1, hJ2, hJ3, hJ4⟩ := cross_y hR1 hadj (fun hcon => hy hcon.symm)
      have hJJ : J' = J := hJu J' hJ3
      subst hJJ
      -- tightness in x at `c` is needed; otherwise the walk returns to `prev`
      have htx : |px C c - (K : ℝ)| < R := by
        by_cases hpx : prev.1 = c.1
        · exfalso
          have hpy : prev.2 ≠ c.2 := by
            intro hcon
            exact h.ne (Prod.ext hpx hcon)
          have : prev.2 = c'.2 := by
            rcases h.prevRow with h1 | h1 <;> rcases h.row with h2 | h2 <;>
              rcases hJ2 with h3 | h3 <;> omega
          exact hne (Prod.ext (by omega) this.symm)
        · exact h.tightX hpx
      refine ⟨hcc', h.col, h.row, by rcases h.col with a | a <;> omega, hJ2, ?_, ?_, ?_, ?_⟩
      · intro hcon; exact absurd hx (fun hh => hcon hh.symm)
      · have : |px C c' - (K : ℝ)| ≤ |px C c' - px C c| + |px C c - (K : ℝ)| := abs_sub_le _ _ _
        rw [abs_sub_comm (px C c') (px C c)] at this
        linarith
      · intro _; exact hJ4
      · linarith [hJ4]
  · -- the step crosses a vertical line
    obtain ⟨K', hK1, hK2, hK3, hK4⟩ := cross_x hR1 hadj (fun hcon => hx hcon.symm)
    have hKK : K' = K := hKu K' hK3
    subst hKK
    by_cases hy : c'.2 = c.2
    · -- vertical line only
      have hty : |py C c - (J : ℝ)| < R := by
        by_cases hpy : prev.2 = c.2
        · exfalso
          have hpx : prev.1 ≠ c.1 := by
            intro hcon
            exact h.ne (Prod.ext hcon hpy)
          have : prev.1 = c'.1 := by
            rcases h.prevCol with h1 | h1 <;> rcases h.col with h2 | h2 <;>
              rcases hK2 with h3 | h3 <;> omega
          exact hne (Prod.ext this.symm (by omega))
        · exact h.tightY hpy
      refine ⟨hcc', h.col, h.row, hK2, by rcases h.row with a | a <;> omega, ?_, ?_, ?_, ?_⟩
      · intro _; exact hK4
      · linarith [hK4]
      · intro hcon; exact absurd hy (fun hh => hcon hh.symm)
      · have : |py C c' - (J : ℝ)| ≤ |py C c' - py C c| + |py C c - (J : ℝ)| := abs_sub_le _ _ _
        rw [abs_sub_comm (py C c') (py C c)] at this
        linarith
    · -- both lines are crossed
      obtain ⟨J', hJ1, hJ2, hJ3, hJ4⟩ := cross_y hR1 hadj (fun hcon => hy hcon.symm)
      have hJJ : J' = J := hJu J' hJ3
      subst hJJ
      exact ⟨hcc', h.col, h.row, hK2, hJ2, fun _ => hK4, by linarith [hK4],
        fun _ => hJ4, by linarith [hJ4]⟩

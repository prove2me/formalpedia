-- Prove2me | solution 1 for GilbertLattice.inv_start
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:21:40.681047+00:00
-- url     : https://prove2.me/submissions/92f2593e-497d-4948-871c-0ca0d52b2f8e

-- Sol generated from Shared/GilbertLatticeLowerBound.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeLowerBound
import Theorems.Thm_GilbertLattice_abs_dx_lt
import Theorems.Thm_GilbertLattice_abs_dy_lt
import Theorems.Thm_GilbertLattice_cross_x
import Theorems.Thm_GilbertLattice_cross_y
import Theorems.Thm_GilbertLattice_no_double_x_trivial
import Theorems.Thm_GilbertLattice_no_double_y_trivial

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
    (h1 : (gilbert R C).Adj c₀ c₁) (h2 : (gilbert R C).Adj c₁ c₂) (hne : c₂ ≠ c₀) :
    ∃ K J : ℤ, Inv R C K J c₁ c₂ ∧ (K = c₀.1 ∨ K = c₀.1 + 1) ∧
      (J = c₀.2 ∨ J = c₀.2 + 1) := by
  have hR1 : R < 1 := by linarith
  -- the horizontal data
  have claimX : ∃ K : ℤ, (K = c₀.1 ∨ K = c₀.1 + 1) ∧ (c₁.1 = K ∨ c₁.1 = K - 1) ∧
      (c₂.1 = K ∨ c₂.1 = K - 1) ∧ (c₁.1 ≠ c₂.1 → |px C c₂ - (K : ℝ)| < R) ∧
      |px C c₂ - (K : ℝ)| < 2 * R := by
    by_cases hx2 : c₂.1 = c₁.1
    · have hx1 : c₁.1 ≠ c₀.1 := by
        intro hcon; exact no_double_x_trivial hR hR0 h1 h2 hne hcon hx2
      obtain ⟨K, hK1, hK2, hK3, hK4⟩ := cross_x hR1 h1 (fun hcon => hx1 hcon.symm)
      refine ⟨K, by omega, hK2, by omega, ?_, ?_⟩
      · intro hcon; exact absurd hx2 (fun hh => hcon hh.symm)
      · have hd := abs_dx_lt h2
        have hb : |px C c₂ - (K : ℝ)| ≤ |px C c₂ - px C c₁| + |px C c₁ - (K : ℝ)| :=
          abs_sub_le _ _ _
        rw [abs_sub_comm (px C c₂) (px C c₁)] at hb
        linarith
    · obtain ⟨K, hK1, hK2, hK3, hK4⟩ := cross_x hR1 h2 (fun hcon => hx2 hcon.symm)
      refine ⟨K, ?_, hK1, hK2, fun _ => hK4, by linarith [hK4]⟩
      by_cases hx1 : c₁.1 = c₀.1
      · omega
      · obtain ⟨K', hK'1, hK'2, hK'3, hK'4⟩ := cross_x hR1 h1 (fun hcon => hx1 hcon.symm)
        have : K' = K := by
          refine int_eq_of_abs_sub_lt_one ?_
          have hb : |((K' : ℝ)) - (K : ℝ)| ≤ |(K' : ℝ) - px C c₁| + |px C c₁ - (K : ℝ)| :=
            abs_sub_le _ _ _
          rw [abs_sub_comm ((K' : ℝ)) (px C c₁)] at hb
          linarith
        omega
  have claimY : ∃ J : ℤ, (J = c₀.2 ∨ J = c₀.2 + 1) ∧ (c₁.2 = J ∨ c₁.2 = J - 1) ∧
      (c₂.2 = J ∨ c₂.2 = J - 1) ∧ (c₁.2 ≠ c₂.2 → |py C c₂ - (J : ℝ)| < R) ∧
      |py C c₂ - (J : ℝ)| < 2 * R := by
    by_cases hy2 : c₂.2 = c₁.2
    · have hy1 : c₁.2 ≠ c₀.2 := by
        intro hcon; exact no_double_y_trivial hR hR0 h1 h2 hne hcon hy2
      obtain ⟨J, hJ1, hJ2, hJ3, hJ4⟩ := cross_y hR1 h1 (fun hcon => hy1 hcon.symm)
      refine ⟨J, by omega, hJ2, by omega, ?_, ?_⟩
      · intro hcon; exact absurd hy2 (fun hh => hcon hh.symm)
      · have hd := abs_dy_lt h2
        have hb : |py C c₂ - (J : ℝ)| ≤ |py C c₂ - py C c₁| + |py C c₁ - (J : ℝ)| :=
          abs_sub_le _ _ _
        rw [abs_sub_comm (py C c₂) (py C c₁)] at hb
        linarith
    · obtain ⟨J, hJ1, hJ2, hJ3, hJ4⟩ := cross_y hR1 h2 (fun hcon => hy2 hcon.symm)
      refine ⟨J, ?_, hJ1, hJ2, fun _ => hJ4, by linarith [hJ4]⟩
      by_cases hy1 : c₁.2 = c₀.2
      · omega
      · obtain ⟨J', hJ'1, hJ'2, hJ'3, hJ'4⟩ := cross_y hR1 h1 (fun hcon => hy1 hcon.symm)
        have : J' = J := by
          refine int_eq_of_abs_sub_lt_one ?_
          have hb : |((J' : ℝ)) - (J : ℝ)| ≤ |(J' : ℝ) - py C c₁| + |py C c₁ - (J : ℝ)| :=
            abs_sub_le _ _ _
          rw [abs_sub_comm ((J' : ℝ)) (py C c₁)] at hb
          linarith
        omega
  obtain ⟨K, hK0, hK1, hK2, hK3, hK4⟩ := claimX
  obtain ⟨J, hJ0, hJ1, hJ2, hJ3, hJ4⟩ := claimY
  exact ⟨K, J, ⟨(h2.ne), hK1, hJ1, hK2, hJ2, hK3, hK4, hJ3, hJ4⟩, hK0, hJ0⟩

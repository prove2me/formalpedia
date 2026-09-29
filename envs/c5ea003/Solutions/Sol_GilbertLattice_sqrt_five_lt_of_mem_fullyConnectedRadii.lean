-- Prove2me | solution 1 for GilbertLattice.sqrt_five_lt_of_mem_fullyConnectedRadii
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:38:06.818734+00:00
-- url     : https://prove2.me/submissions/ac5635f1-7932-4105-988b-21530d19baea

-- Sol generated from Shared/GilbertLatticeDiagonalCut.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeCriticalRadii
import Definitions.Def_Shared_GilbertLatticeDiagonalCut
import Theorems.Thm_GilbertLattice_five_le_sqdist_diag
import Theorems.Thm_GilbertLattice_not_adj_of_le_sqdist
import Theorems.Thm_GilbertLattice_radius_pos_of_adj

/-!
# The exact value of the full-connectivity radius: `R_full = √5`

For the model *Gilbert's disc model conditioned on the square lattice* (one point per
cell of `ℤ²`, two points joined when their distance is `< R`) the file
`GilbertLatticeCriticalRadii.lean` bounds the radius of *full connectivity*

`R_full = inf {R : for every placement of the points, the graph is connected}`

between `√17 / 2 ≈ 2.0616` (a horizontal cut) and `√5 ≈ 2.2360`.

This file closes the gap: it produces a placement built along a **diagonal** cut for
which every crossing pair of points is at distance at least `√5`, so that the graph is
disconnected for every `R ≤ √5`.  Together with the upper bound of
`GilbertLatticeConnectivity.lean` this gives the exact value

* `GilbertLattice.Rfull_eq_sqrt_five` : `R_full = √5`,

and even the exact description of the set of radii of full connectivity,

* `GilbertLattice.fullyConnectedRadii_eq` : `{R : every placement is connected} = (√5, ∞)`.

## The diagonal configuration

Cells are split along the diagonal: `c` is *upper* when `c.1 ≤ c.2` and *lower*
otherwise.  The point of an upper cell is pushed to the top-left corner of the cell,
the point of a lower cell to the bottom-right corner.  If `c` is upper and `c'` is
lower, the displacement between the two points is `(u, v)` with

`u = c.1 - c'.1 - 1`,  `v = c.2 + 1 - c'.2`,  and  `v ≥ u + 3`;

over the integers this forces `u² + v² ≥ 5` (`GilbertLattice.five_le_sq_add_sq`), the
minimum `5` being attained at `(u, v) = (-1, 2)` and `(-2, 1)`.  Note that the naive
continuous bound would only give `u² + v² ≥ 9/2`: the value `5` is genuinely arithmetic.
-/

open GilbertLattice









/-- No edge of the diagonal configuration crosses the diagonal when `R² ≤ 5`. -/
lemma diagConfig_no_crossing_edge {R : ℝ} (hR : R ^ 2 ≤ 5) {c c' : ℤ × ℤ}
    (hc : c.1 ≤ c.2) (hc' : ¬ c'.1 ≤ c'.2) : ¬ (gilbert R diagConfig).Adj c c' :=
  not_adj_of_le_sqdist (le_trans hR (five_le_sqdist_diag hc hc'))

/-- The set of cells above the diagonal is stable under adjacency when `R² ≤ 5`. -/
lemma diagConfig_upper_closed {R : ℝ} (hR : R ^ 2 ≤ 5) {c c' : ℤ × ℤ}
    (hadj : (gilbert R diagConfig).Adj c c') (hc : c.1 ≤ c.2) : c'.1 ≤ c'.2 := by
  by_contra hcon
  exact diagConfig_no_crossing_edge hR hc hcon hadj

/-- The set of cells above the diagonal is stable under reachability when `R² ≤ 5`. -/
lemma diagConfig_reachable_upper {R : ℝ} (hR : R ^ 2 ≤ 5) {c c' : ℤ × ℤ}
    (h : (gilbert R diagConfig).Reachable c c') (hc : c.1 ≤ c.2) : c'.1 ≤ c'.2 := by
  obtain ⟨w⟩ := h
  revert hc
  induction w with
  | nil => exact id
  | cons hadj w ih => exact fun hc => ih (diagConfig_upper_closed hR hadj hc)

/-- For `R² ≤ 5` the diagonal configuration separates the cell `(0,0)` from `(0,-1)`. -/
theorem diagConfig_not_reachable {R : ℝ} (hR : R ^ 2 ≤ 5) :
    ¬ (gilbert R diagConfig).Reachable (0, 0) (0, -1) := by
  intro h
  have := diagConfig_reachable_upper hR h (by norm_num)
  norm_num at this

/-- **Lower bound for the radius of full connectivity.**  For every `R ≤ √5` there is a
placement of one point per cell whose Gilbert graph is disconnected. -/
theorem diagConfig_not_connected {R : ℝ} (hR : R ^ 2 ≤ 5) :
    ¬ (gilbert R diagConfig).Connected := fun h =>
  diagConfig_not_reachable hR (h.preconnected (0, 0) (0, -1))





open GilbertLattice in
theorem solution{R : ℝ} (hR : R ∈ fullyConnectedRadii) :
    Real.sqrt 5 < R := by
  by_contra hcon
  push_neg at hcon
  have hRpos : 0 < R := by
    by_contra hle
    push_neg at hle
    obtain ⟨w⟩ := (hR diagConfig).preconnected (0, 0) (1, 0)
    cases w with
    | cons hadj w' => exact absurd (radius_pos_of_adj hadj) (not_lt.2 hle)
  have hs : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
  have hsnn : (0 : ℝ) ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  have hR2 : R ^ 2 ≤ 5 := by nlinarith
  exact diagConfig_not_connected hR2 (hR diagConfig)

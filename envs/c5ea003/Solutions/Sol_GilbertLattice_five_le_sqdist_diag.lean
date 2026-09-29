-- Prove2me | solution 1 for GilbertLattice.five_le_sqdist_diag
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:35:06.716734+00:00
-- url     : https://prove2.me/submissions/2620d82a-8574-4d97-840b-6b8c2a028eb0

-- Sol generated from Shared/GilbertLatticeDiagonalCut.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Definitions.Def_Shared_GilbertLatticeCriticalRadii
import Definitions.Def_Shared_GilbertLatticeDiagonalCut

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

/-- **The integral gap estimate.**  If two integers satisfy `v ≥ u + 3`, then
`u² + v² ≥ 5`.  (Over the reals the optimum would be `9/2`.) -/
lemma five_le_sq_add_sq {u v : ℤ} (h : u + 3 ≤ v) : 5 ≤ u ^ 2 + v ^ 2 := by
  rcases le_or_gt u (-3) with hu | hu
  · nlinarith [sq_nonneg v]
  rcases le_or_gt 0 u with hu0 | hu0
  · nlinarith [sq_nonneg u]
  · interval_cases u <;> nlinarith



lemma px_diag_upper {c : ℤ × ℤ} (h : c.1 ≤ c.2) : px diagConfig c = (c.1 : ℝ) := by
  simp [px, diagConfig, diagOff, h]

lemma py_diag_upper {c : ℤ × ℤ} (h : c.1 ≤ c.2) : py diagConfig c = (c.2 : ℝ) + 1 := by
  simp [py, diagConfig, diagOff, h]

lemma px_diag_lower {c : ℤ × ℤ} (h : ¬ c.1 ≤ c.2) : px diagConfig c = (c.1 : ℝ) + 1 := by
  simp [px, diagConfig, diagOff, h]

lemma py_diag_lower {c : ℤ × ℤ} (h : ¬ c.1 ≤ c.2) : py diagConfig c = (c.2 : ℝ) := by
  simp [py, diagConfig, diagOff, h]











open GilbertLattice in
theorem solution{c c' : ℤ × ℤ} (hc : c.1 ≤ c.2) (hc' : ¬ c'.1 ≤ c'.2) :
    5 ≤ sqdist diagConfig c c' := by
  set u : ℤ := c.1 - c'.1 - 1 with hu
  set v : ℤ := c.2 + 1 - c'.2 with hv
  have hkey : u + 3 ≤ v := by simp only [hu, hv]; omega
  have hint : (5 : ℤ) ≤ u ^ 2 + v ^ 2 := five_le_sq_add_sq hkey
  have hreal : (5 : ℝ) ≤ ((u : ℝ)) ^ 2 + ((v : ℝ)) ^ 2 := by exact_mod_cast hint
  have hx : px diagConfig c - px diagConfig c' = (u : ℝ) := by
    rw [px_diag_upper hc, px_diag_lower hc', hu]; push_cast; ring
  have hy : py diagConfig c - py diagConfig c' = (v : ℝ) := by
    rw [py_diag_upper hc, py_diag_lower hc', hv]; push_cast; ring
  unfold sqdist
  rw [hx, hy]
  exact hreal

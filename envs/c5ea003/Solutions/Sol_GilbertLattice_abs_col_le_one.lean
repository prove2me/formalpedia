-- Prove2me | solution 1 for GilbertLattice.abs_col_le_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:15:30.306615+00:00
-- url     : https://prove2.me/submissions/32dca0e9-0695-4a3b-9f32-a7fb56e3e753

-- Sol generated from Shared/GilbertLatticeBasic.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Theorems.Thm_GilbertLattice_abs_dx_lt

/-!
# Gilbert's disc model conditioned on the square lattice: the model

This file sets up the deterministic skeleton of the percolation model studied in
*Gilbert's disc model conditioned on the square lattice*.

One point is placed in each cell of the grid `ℤ²` (in the random model the point is
uniform in its cell; all the results formalised here are statements about *all*
admissible placements, hence they hold for every realisation of the random model).
Two points are joined by an edge when their Euclidean distance is smaller than a fixed
radius `R`.

* `GilbertLattice.Config` — a placement of one point per cell, encoded by its offset
  in the closed unit square `[0,1]²`.
* `GilbertLattice.px`, `GilbertLattice.py` — the coordinates of the point of a cell.
* `GilbertLattice.gilbert` — the resulting graph on the set of cells `ℤ × ℤ`.

The elementary facts proved here: an edge forces both coordinate differences to be
`< R`, an edge forces `0 < R`, for `R ≤ 1` neighbouring cells differ by at most one in
each coordinate, and the model is monotone in `R`.
-/

open GilbertLattice





















open GilbertLattice in
lemma solution{R : ℝ} (hR : R ≤ 1) {C : Config} {c c' : ℤ × ℤ}
    (h : (gilbert R C).Adj c c') : |c'.1 - c.1| ≤ 1 := by
  have hx := abs_dx_lt h
  have h1 := C.off_nonneg_fst c
  have h2 := C.off_le_one_fst c
  have h3 := C.off_nonneg_fst c'
  have h4 := C.off_le_one_fst c'
  have key : |((c'.1 - c.1 : ℤ) : ℝ)| < 2 := by
    have : ((c'.1 - c.1 : ℤ) : ℝ) = (px C c' - px C c) + ((C.off c).1 - (C.off c').1) := by
      unfold px; push_cast; ring
    rw [this]
    have := abs_lt.1 hx
    rw [abs_lt]
    constructor <;> [linarith [this.1, this.2]; linarith [this.1, this.2]]
  have h5 : ((|c'.1 - c.1| : ℤ) : ℝ) < 2 := by rw [Int.cast_abs]; exact key
  have h6 : |c'.1 - c.1| < (2 : ℤ) := by exact_mod_cast h5
  omega

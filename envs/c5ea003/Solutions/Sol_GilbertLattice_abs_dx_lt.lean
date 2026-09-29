-- Prove2me | solution 1 for GilbertLattice.abs_dx_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:14:16.571217+00:00
-- url     : https://prove2.me/submissions/635fc71c-42a9-4c51-ab72-3e00e0ab5365

-- Sol generated from Shared/GilbertLatticeBasic.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2

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
lemma solution{R : ℝ} {C : Config} {c c' : ℤ × ℤ} (h : (gilbert R C).Adj c c') :
    |px C c - px C c'| < R := by
  refine lt_of_le_of_lt ?_ h.2
  rw [pdist, ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by unfold sqdist; nlinarith [sq_nonneg (py C c - py C c')])

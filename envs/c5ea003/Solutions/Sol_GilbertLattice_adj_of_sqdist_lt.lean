-- Prove2me | solution 1 for GilbertLattice.adj_of_sqdist_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:12:30.957825+00:00
-- url     : https://prove2.me/submissions/6e1237e1-4927-4b18-a5df-a48867116438

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
lemma solution{R : ℝ} (hR : 0 < R) {C : Config} {c c' : ℤ × ℤ} (hne : c ≠ c')
    (h : sqdist C c c' < R ^ 2) : (gilbert R C).Adj c c' := by
  exact ⟨hne, (Real.sqrt_lt' hR).2 h⟩

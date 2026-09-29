-- Prove2me | Theorems.Thm_GilbertLattice_radius_pos_of_adj
-- name    : GilbertLattice.radius_pos_of_adj
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T19:24:42.059991+00:00
-- url     : https://prove2.me/theorems/79681e75-c7a4-477a-b76e-e089c571354e
-- title:
--   Radius pos of adj
-- statement:
--   Formal statement of `GilbertLattice.radius_pos_of_adj` from the Aether Catalog (Shared). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem GilbertLattice.radius_pos_of_adj{R : ℝ} {C : Config} {c c' : ℤ × ℤ} (h : (gilbert R C).Adj c c') :
--       0 < R := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/GilbertLatticeBasic.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/GilbertLatticeBasic.lean#L70

-- Thm stub generated from Shared/GilbertLatticeBasic.lean
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

theorem GilbertLattice.radius_pos_of_adj{R : ℝ} {C : Config} {c c' : ℤ × ℤ} (h : (gilbert R C).Adj c c') :
    0 < R := by sorry

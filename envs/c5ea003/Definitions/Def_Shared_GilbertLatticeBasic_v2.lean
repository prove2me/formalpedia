-- Prove2me | Definitions.Def_Shared_GilbertLatticeBasic_v2
-- name    : Shared_GilbertLatticeBasic_v2
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T14:59:19.7184+00:00
-- url     : https://prove2.me/theorems/b73051aa-6407-4296-a3b5-530134b260a8
-- title:
--   Aether Catalog definitions — Shared_GilbertLatticeBasic_v2
-- statement:
--   Definition bundle for the Aether Catalog module Shared.GilbertLatticeBasic, transplanted by skeleton subtraction; supplies the types and constants the catalog theorems import.

-- Def bundle generated from Shared/GilbertLatticeBasic.lean by skeleton subtraction
import Mathlib

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

namespace GilbertLattice

/-- A *configuration*: the offset, inside its own cell, of the point of each cell of
the grid `ℤ²`.  Offsets range over the closed unit square `[0,1]²`. -/
structure Config where
  /-- The offset of the point of a given cell. -/
  off : ℤ × ℤ → ℝ × ℝ
  off_nonneg_fst : ∀ c, 0 ≤ (off c).1
  off_nonneg_snd : ∀ c, 0 ≤ (off c).2
  off_le_one_fst : ∀ c, (off c).1 ≤ 1
  off_le_one_snd : ∀ c, (off c).2 ≤ 1

/-- The first coordinate of the point placed in cell `c`. -/
def px (C : Config) (c : ℤ × ℤ) : ℝ := (c.1 : ℝ) + (C.off c).1

/-- The second coordinate of the point placed in cell `c`. -/
def py (C : Config) (c : ℤ × ℤ) : ℝ := (c.2 : ℝ) + (C.off c).2

/-- Squared Euclidean distance between the points of two cells. -/
def sqdist (C : Config) (c c' : ℤ × ℤ) : ℝ :=
  (px C c - px C c') ^ 2 + (py C c - py C c') ^ 2

lemma sqdist_comm (C : Config) (c c' : ℤ × ℤ) : sqdist C c c' = sqdist C c' c := by
  unfold sqdist; ring


/-- Euclidean distance between the points of two cells. -/
noncomputable def pdist (C : Config) (c c' : ℤ × ℤ) : ℝ := Real.sqrt (sqdist C c c')

/-- The Gilbert graph of a configuration: two distinct cells are joined when the
Euclidean distance between their points is `< R`. -/
def gilbert (R : ℝ) (C : Config) : SimpleGraph (ℤ × ℤ) where
  Adj c c' := c ≠ c' ∧ pdist C c c' < R
  symm := by
    rintro a b ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    unfold pdist at h2 ⊢
    rwa [sqdist_comm]
  loopless := ⟨fun _ h => h.1 rfl⟩












end GilbertLattice



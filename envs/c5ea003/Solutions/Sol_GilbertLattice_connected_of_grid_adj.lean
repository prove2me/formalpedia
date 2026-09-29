-- Prove2me | solution 1 for GilbertLattice.connected_of_grid_adj
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:12:31.623913+00:00
-- url     : https://prove2.me/submissions/7a18184e-0751-4f94-92e7-f3df47417440

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
lemma solution{R : ℝ} {C : Config}
    (hh : ∀ i j : ℤ, (gilbert R C).Adj (i, j) (i + 1, j))
    (hv : ∀ i j : ℤ, (gilbert R C).Adj (i, j) (i, j + 1)) : (gilbert R C).Connected := by
  have horiz : ∀ i i' j : ℤ, (gilbert R C).Reachable (i, j) (i', j) := by
    intro i i' j
    have key : ∀ k : ℤ, (gilbert R C).Reachable (i, j) (i + k, j) := by
      intro k
      induction k using Int.induction_on with
      | zero => simp
      | succ n ih =>
          refine ih.trans ?_
          have h := (hh (i + (n : ℤ)) j).reachable
          have e : i + (n : ℤ) + 1 = i + ((n : ℤ) + 1) := by ring
          rwa [e] at h
      | pred n ih =>
          refine ih.trans ?_
          have h := (hh (i + (-(n : ℤ) - 1)) j).reachable
          have e : i + (-(n : ℤ) - 1) + 1 = i + -(n : ℤ) := by ring
          rw [e] at h
          exact h.symm
    have := key (i' - i)
    simpa using this
  have vert : ∀ i j j' : ℤ, (gilbert R C).Reachable (i, j) (i, j') := by
    intro i j j'
    have key : ∀ k : ℤ, (gilbert R C).Reachable (i, j) (i, j + k) := by
      intro k
      induction k using Int.induction_on with
      | zero => simp
      | succ n ih =>
          refine ih.trans ?_
          have h := (hv i (j + (n : ℤ))).reachable
          have e : j + (n : ℤ) + 1 = j + ((n : ℤ) + 1) := by ring
          rwa [e] at h
      | pred n ih =>
          refine ih.trans ?_
          have h := (hv i (j + (-(n : ℤ) - 1))).reachable
          have e : j + (-(n : ℤ) - 1) + 1 = j + -(n : ℤ) := by ring
          rw [e] at h
          exact h.symm
    have := key (j' - j)
    simpa using this
  rw [SimpleGraph.connected_iff]
  refine ⟨?_, ⟨(0, 0)⟩⟩
  intro c c'
  have h1 : (gilbert R C).Reachable (c.1, c.2) (c'.1, c.2) := horiz _ _ _
  have h2 : (gilbert R C).Reachable (c'.1, c.2) (c'.1, c'.2) := vert _ _ _
  simpa using h1.trans h2

-- Prove2me | solution 1 for GilbertLattice.connected_of_sqrt_five_lt
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T23:32:14.633597+00:00
-- url     : https://prove2.me/submissions/9fbf1944-f30f-49ec-8360-31e0d0ca0102

-- Sol generated from Shared/GilbertLatticeConnectivity.lean
import Mathlib
import Definitions.Def_Shared_GilbertLatticeBasic_v2
import Theorems.Thm_GilbertLattice_adj_horiz
import Theorems.Thm_GilbertLattice_adj_vert
import Theorems.Thm_GilbertLattice_connected_of_grid_adj

/-!
# Full connectivity of the conditioned Gilbert model for large radii

The third critical radius of the model is

`R_full = inf {R : for every placement of the points, all points are connected}`.

Two points sitting in two cells sharing an edge are at distance at most
`√(2² + 1²) = √5`, whatever the placement.  Consequently, as soon as `R > √5`, every
placement produces a graph containing the whole nearest-neighbour grid graph of `ℤ²`,
which is connected.  This gives `R_full ≤ √5`; the companion file
`GilbertLatticeConstructions.lean` provides the lower bound `R_full ≥ √17 / 2`.
-/

open GilbertLattice

variable {R : ℝ} (C : Config)







open GilbertLattice in
theorem solution(hR : Real.sqrt 5 < R) : (gilbert R C).Connected :=
  connected_of_grid_adj (fun i j => adj_horiz C hR i j) (fun i j => adj_vert C hR i j)

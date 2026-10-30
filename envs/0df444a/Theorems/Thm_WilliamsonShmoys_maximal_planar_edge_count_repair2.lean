-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_repair2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_repair2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:35:12.628226+00:00
-- url     : https://prove2.me/theorems/d1224858-4ac7-4a8f-9342-ed422c097a3c
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   An inclusion-maximal drawable graph on at least three vertices has exactly 3|V|−6 edges. This removes the planar-topology and Euler-counting obligation from the parent; a proof route is to show maximality forces connectedness and triangular faces, then count with Euler’s formula, handling the three-vertex boundary as K₃. That topological argument remains the core open obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_repair2
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hmax : ∀ T : SimpleGraph V, S ≤ T →
      WilliamsonShmoys.HasPlanarDrawingOn T → T = S) :
    S.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry

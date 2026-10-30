-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_for_triangulation_extension
-- name    : WilliamsonShmoys.maximal_drawable_edge_count_for_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:30:17.366912+00:00
-- url     : https://prove2.me/theorems/61c7008e-00a5-4f97-a027-3293367da780
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable graph with at least three vertices that is maximal among drawable supergraphs on those vertices has exactly three times the vertex count minus six edges. The proof establishes that maximality forces a connected triangulated planar embedding, then applies Euler's formula and counts incidences between edges and faces.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_edge_count_for_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (Z : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hZdraw : WilliamsonShmoys.HasPlanarDrawingOn Z)
    (hmax : ∀ W : SimpleGraph V, Z ≤ W →
      WilliamsonShmoys.HasPlanarDrawingOn W → W ≤ Z) :
    Z.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  sorry

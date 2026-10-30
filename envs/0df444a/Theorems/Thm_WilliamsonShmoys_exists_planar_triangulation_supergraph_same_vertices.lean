-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_supergraph_same_vertices
-- name    : WilliamsonShmoys.exists_planar_triangulation_supergraph_same_vertices
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:57:41.94782+00:00
-- url     : https://prove2.me/theorems/2a9755e4-bee4-43ad-b448-9ad5172e3d2d
-- title:
--   Planar triangulation extension on the same vertex set
-- statement:
--   Every drawable simple graph on a finite ordered vertex set of at least three vertices has a drawable supergraph on the same vertex set with exactly 3|V|−6 edges. The parent uses maximality to identify this supergraph with the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_supergraph_same_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hS : WilliamsonShmoys.HasPlanarDrawingOn S) :
    ∃ T : SimpleGraph V,
      S ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
      T.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

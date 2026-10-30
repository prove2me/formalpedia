-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph_edge_count
-- name    : WilliamsonShmoys.planar_maximal_supergraph_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:40:47.170293+00:00
-- url     : https://prove2.me/theorems/8bed89f5-b4a1-4e0c-8939-cbf59f18f35d
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph that is inclusion-maximal among drawable supergraphs on its vertex type, with at least three vertices, has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ R : SimpleGraph V,
      M ≤ R →
      WilliamsonShmoys.HasPlanarDrawingOn R →
      R ≤ M) :
    3 * Fintype.card V - 6 = M.edgeSet.ncard := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulated_extension_maximal_supergraph_edge_count
-- name    : WilliamsonShmoys.planar_triangulated_extension_maximal_supergraph_edge_count
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T11:05:32.075495+00:00
-- url     : https://prove2.me/theorems/51bf81b4-48bc-4660-b9e1-3005ea79cb82
-- title:
--   Edge count of a maximal drawable supergraph
-- statement:
--   A drawable simple graph with at least three vertices that is maximal among drawable supergraphs on the same vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulated_extension_maximal_supergraph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V,
      M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_planar_drawing_edge_maximal_3e41a808
-- name    : WilliamsonShmoys.edge_count_of_planar_drawing_edge_maximal_3e41a808
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T02:20:24.606985+00:00
-- url     : https://prove2.me/theorems/25a6b228-75bf-4989-8674-1aa60ff232ed
-- title:
--   An edge-maximal drawable graph has the triangulation edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable simple supergraph on the same vertex type has exactly 3|V|−6 edges. The proof uses face insertion to force a triangulated plane embedding, then Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edge_count_of_planar_drawing_edge_maximal_3e41a808
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → H = K) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

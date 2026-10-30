-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_b80c2ba3_repair2_maximal_graph_edge_count
-- name    : WilliamsonShmoys.planar_drawing_triangulation_extension_b80c2ba3_repair2_maximal_graph_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T07:27:36.088843+00:00
-- url     : https://prove2.me/theorems/eaa99414-a46b-4eff-9f57-b4eb1f7b5f38
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three vertices that is inclusion-maximal among drawable supergraphs on the same vertex set has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_triangulation_extension_b80c2ba3_repair2_maximal_graph_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P →
      N.edgeSet ⊆ P.edgeSet →
      P.edgeSet ⊆ N.edgeSet) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

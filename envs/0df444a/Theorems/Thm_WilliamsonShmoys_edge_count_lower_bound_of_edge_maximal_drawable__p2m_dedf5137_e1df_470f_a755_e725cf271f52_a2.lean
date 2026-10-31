-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_lower_bound_of_edge_maximal_drawable__p2m_dedf5137_e1df_470f_a755_e725cf271f52_a2
-- name    : WilliamsonShmoys.edge_count_lower_bound_of_edge_maximal_drawable__p2m_dedf5137_e1df_470f_a755_e725cf271f52_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:13:10.989789+00:00
-- url     : https://prove2.me/theorems/b3e06432-ff08-463e-bcdc-60830368f3ac
-- title:
--   Edge lower bound for a maximal drawable graph
-- statement:
--   If a drawable graph on at least three vertices is maximal among drawable supergraphs on the same vertex type, then it has at least `3|V| - 6` edges. The independent proof route is to use maximality to show that a planar embedding has triangular faces, then combine Euler’s formula with the count that each edge borders two face sides. This is the remaining topological core of the reduction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.edge_count_lower_bound_of_edge_maximal_drawable__p2m_dedf5137_e1df_470f_a755_e725cf271f52_a2 {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G) (hV : 3 ≤ Fintype.card V) (hMax : ∀ L : SimpleGraph V, G ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = G) : 3 * Fintype.card V - 6 ≤ G.edgeSet.ncard := by sorry

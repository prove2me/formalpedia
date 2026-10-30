-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_simple_graph_edge_count_lower_bound
-- name    : WilliamsonShmoys.maximal_drawable_simple_graph_edge_count_lower_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:19:05.763679+00:00
-- url     : https://prove2.me/theorems/79b24d34-bbf5-4bde-b231-9f9d2af77875
-- title:
--   Maximal drawable graphs have enough edges
-- statement:
--   An inclusion-maximal graph with the specified crossing-free drawing and at least three vertices has at least 3|V|−6 edges. A proof route derives an embedding, establishes that maximality forces triangular faces, and combines face-edge incidence counting with Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_simple_graph_edge_count_lower_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : ∀ U : SimpleGraph V,
      G ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = G) :
    3 * Fintype.card V - 6 ≤ G.edgeSet.ncard := by sorry

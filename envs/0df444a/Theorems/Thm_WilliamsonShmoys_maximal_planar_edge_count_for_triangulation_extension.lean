-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_extension
-- name    : WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T19:46:47.758021+00:00
-- url     : https://prove2.me/theorems/cddbfaf1-a37d-43b0-a363-d40be2d35f07
-- title:
--   An edge maximal planar drawing has the triangulation edge count
-- statement:
--   A finite simple graph on at least three vertices that has a planar drawing and admits no strict planar supergraph has exactly 3|V|−6 edges. This isolates the topological counting core: establish that maximality forces every face to be triangular, then use Euler’s formula. At |V| = 3, the maximal graph is the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hMax : ∀ H : SimpleGraph V, G.edgeSet ⊂ H.edgeSet →
      ¬ WilliamsonShmoys.HasPlanarDrawingOn H) :
    G.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_triangulation_extension
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph_for_triangulation_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T19:40:15.62074+00:00
-- url     : https://prove2.me/theorems/a623a3f4-ea68-46d3-bd6e-2ba96f2f15a0
-- title:
--   A planar drawing has an edge maximal planar extension
-- statement:
--   Every finite graph with a planar drawing has a planar extension on the same vertex type that admits no strict planar supergraph. This removes the finite maximality step from the parent. The hypotheses include the three-vertex boundary case; the vertex lower bound is retained for compatibility with the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_planar_supergraph_for_triangulation_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ G : SimpleGraph V,
      M.edgeSet ⊆ G.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn G ∧
      ∀ H : SimpleGraph V, G.edgeSet ⊂ H.edgeSet →
        ¬ WilliamsonShmoys.HasPlanarDrawingOn H := by sorry

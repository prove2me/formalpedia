-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_edge_completion_maximal_extension
-- name    : WilliamsonShmoys.planar_graph_edge_completion_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T06:56:00.436733+00:00
-- url     : https://prove2.me/theorems/04821ff3-2fd3-480c-9353-6d090f1667c5
-- title:
--   Every finite planar graph has a maximal planar extension
-- statement:
--   Any finite graph with a planar drawing has a planar supergraph on the same vertex set that has no strictly larger planar supergraph on that vertex set. The proof route is to choose an edge-maximal element among the finitely many edge sets containing the original graph that admit planar drawings. The child removes the extension and maximality construction from the parent; its main formal obligation is to show that the drawing predicate is preserved as edges are considered and that finite maximality applies.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_edge_completion_maximal_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V,
        N.edgeSet ⊆ K.edgeSet →
        WilliamsonShmoys.HasPlanarDrawingOn K →
        K.edgeSet ⊆ N.edgeSet := by sorry

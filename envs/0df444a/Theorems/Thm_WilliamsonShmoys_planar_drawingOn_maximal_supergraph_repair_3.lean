-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_maximal_supergraph_repair_3
-- name    : WilliamsonShmoys.planar_drawingOn_maximal_supergraph_repair_3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:50:36.294346+00:00
-- url     : https://prove2.me/theorems/003e61af-cc2a-4c6b-bff7-441e8a15f72e
-- title:
--   Extend a planar drawing to a maximal drawable supergraph
-- statement:
--   Extend the given drawable graph to an inclusion-maximal drawable supergraph on the same finite vertex type. The maximality clause says that every drawable supergraph of N has the same edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_maximal_supergraph_repair_3 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hM : WilliamsonShmoys.HasPlanarDrawingOn M) (hV : 3 ≤ Fintype.card V) : ∃ N : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn N ∧ M.edgeSet ⊆ N.edgeSet ∧ (∀ H : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn H → N.edgeSet ⊆ H.edgeSet → H.edgeSet ⊆ N.edgeSet) := by sorry

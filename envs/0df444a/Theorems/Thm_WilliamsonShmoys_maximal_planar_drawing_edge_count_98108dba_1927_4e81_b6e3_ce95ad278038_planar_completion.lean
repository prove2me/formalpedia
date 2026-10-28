-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_98108dba_1927_4e81_b6e3_ce95ad278038_planar_completion
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_98108dba_1927_4e81_b6e3_ce95ad278038_planar_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T12:23:19.693763+00:00
-- url     : https://prove2.me/theorems/2a77893c-8379-4827-8265-76a9c861f3f2
-- title:
--   Completion of a planar drawing to a triangulation
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of size at least three is a subgraph of a drawable graph on the same vertices whose edge count is exactly three times the vertex count minus six. The lemma supplies the completion used in the parent: maximality forces that completion to equal the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_98108dba_1927_4e81_b6e3_ce95ad278038_planar_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    ∃ M : SimpleGraph V, L ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

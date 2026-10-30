-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulation_completion_with_exact_edge_count
-- name    : WilliamsonShmoys.exists_triangulation_completion_with_exact_edge_count
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T12:30:52.502344+00:00
-- url     : https://prove2.me/theorems/07e1ae9f-021c-4dea-90ca-dda5cc25e684
-- title:
--   Planar drawing admits a triangulation completion
-- statement:
--   Any finite graph with at least three vertices that has the supplied crossing-free drawing has a planar supergraph on the same vertex type whose edge count is exactly three times the number of vertices minus six. The completion is obtained by adding noncrossing edges until the embedding is triangulated; the parent uses maximality to show that this completion has the same edge set as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_triangulation_completion_with_exact_edge_count
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V) :
    ∃ R : SimpleGraph V,
      Q.edgeSet ⊆ R.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn R ∧
      R.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

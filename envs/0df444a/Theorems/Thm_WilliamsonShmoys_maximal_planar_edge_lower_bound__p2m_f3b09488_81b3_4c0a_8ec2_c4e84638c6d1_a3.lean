-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a3
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T21:42:42.887225+00:00
-- url     : https://prove2.me/theorems/ae8a5b35-4353-4996-a589-b8042ebe71b7
-- title:
--   Maximal drawable graphs have at least 3n−6 edges
-- statement:
--   If `H` has a crossing-free drawing and every drawable supergraph on the same vertex type is contained in `H`, with at least three vertices, then `H` has at least `3|V|−6` edges. The proof route is to use maximality to show that the drawing cannot have a face with room for another edge, establish the resulting triangulation structure, and count face-edge incidences using Euler’s formula. This isolates the lower-bound and maximality work from the parent; it does not assume connectedness or omit the cardinality condition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Data.Set.Card

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_f3b09488_81b3_4c0a_8ec2_c4e84638c6d1_a3
    {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V)
    (hMax : WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ H.edgeSet.ncard := by sorry

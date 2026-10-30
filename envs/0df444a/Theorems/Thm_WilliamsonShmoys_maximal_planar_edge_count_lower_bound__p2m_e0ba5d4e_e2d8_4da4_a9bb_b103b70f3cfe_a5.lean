-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_e0ba5d4e_e2d8_4da4_a9bb_b103b70f3cfe_a5
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e0ba5d4e_e2d8_4da4_a9bb_b103b70f3cfe_a5
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T01:45:39.448841+00:00
-- url     : https://prove2.me/theorems/4ebee2da-fb63-48f9-8015-84846516bd66
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A drawable graph that is maximal under drawable edge-set extension, with at least three vertices, has at least 3|V|−6 edges. The three-vertex case follows directly from maximality; for larger graphs, a proof route connects components and triangulates the embedding, then applies Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_e0ba5d4e_e2d8_4da4_a9bb_b103b70f3cfe_a5
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hV : 3 <= Fintype.card V)
    (hmax : forall R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R ->
      Set.Subset Q.edgeSet R.edgeSet -> Set.Subset R.edgeSet Q.edgeSet) :
    3 * Fintype.card V - 6 <= Q.edgeSet.ncard := by sorry

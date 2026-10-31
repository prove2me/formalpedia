-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_embedding_edge_count__p2m_a731e400_b1bb_4df1_b39d_695b2e00a6cf_a1
-- name    : WilliamsonShmoys.maximal_planar_embedding_edge_count__p2m_a731e400_b1bb_4df1_b39d_695b2e00a6cf_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:48:58.513294+00:00
-- url     : https://prove2.me/theorems/22a5b5f7-3235-4182-9d94-02fe344a3dcd
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A finite graph on at least three vertices that is maximal among graphs admitting the specified crossing-free drawing has exactly 3|V| − 6 edges. This packages the substantive planar-topology step; combined with f = 2|V| − 4, it yields both requested face-count equations.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_embedding_edge_count__p2m_a731e400_b1bb_4df1_b39d_695b2e00a6cf_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hDraw : HasPlanarDrawingOn T) (hV : 3 <= Fintype.card V) (hMax : forall N : SimpleGraph V, T <= N -> HasPlanarDrawingOn N -> N <= T) : T.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

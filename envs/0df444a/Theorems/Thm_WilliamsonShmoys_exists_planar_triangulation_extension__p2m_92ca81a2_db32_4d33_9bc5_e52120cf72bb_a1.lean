-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_triangulation_extension__p2m_92ca81a2_db32_4d33_9bc5_e52120cf72bb_a1
-- name    : WilliamsonShmoys.exists_planar_triangulation_extension__p2m_92ca81a2_db32_4d33_9bc5_e52120cf72bb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:15:35.946916+00:00
-- url     : https://prove2.me/theorems/3ea1a2df-ff39-4335-a398-1933022707b1
-- title:
--   Planar triangulated extension with exact edge count
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing has a planar simple supergraph on the same vertices whose edge count is exactly 3n − 6, with the original edge count no larger than the extension's.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_planar_triangulation_extension__p2m_92ca81a2_db32_4d33_9bc5_e52120cf72bb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V,
      H ≤ G ∧
      WilliamsonShmoys.HasPlanarDrawingOn G ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel G.Adj := Classical.decRel G.Adj
       H.edgeFinset.card ≤ G.edgeFinset.card ∧
       G.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry

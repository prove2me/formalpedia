-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_edgeSet_ncard_mono__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
-- name    : WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:07:53.867665+00:00
-- url     : https://prove2.me/theorems/95007712-6936-4c29-bb9d-219399411eea
-- title:
--   Monotonicity of finite simple graph edge counts
-- statement:
--   If one finite simple graph is a subgraph of another on the same vertex type, its edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono__p2m_2a90ede6_b2ad_40d4_a25e_8e3e873838ed_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V) (hHK : H ≤ K) :
    H.edgeSet.ncard ≤ K.edgeSet.ncard := by sorry

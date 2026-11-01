-- Prove2me | Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
-- name    : WilliamsonShmoys.edgeSet_ncard_mono__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:36:26.974067+00:00
-- url     : https://prove2.me/theorems/9daded41-2cef-4e33-92eb-2c5897dea925
-- title:
--   Edge-count monotonicity under graph inclusion
-- statement:
--   If every edge of one finite simple graph is an edge of another, the first graph's edge count is no larger.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edgeSet_ncard_mono__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hsub : ∀ u v, G.Adj u v → H.Adj u v) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by sorry

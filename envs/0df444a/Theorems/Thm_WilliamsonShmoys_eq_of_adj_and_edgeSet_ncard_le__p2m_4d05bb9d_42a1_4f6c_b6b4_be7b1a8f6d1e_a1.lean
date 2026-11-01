-- Prove2me | Theorems.Thm_WilliamsonShmoys_eq_of_adj_and_edgeSet_ncard_le__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
-- name    : WilliamsonShmoys.eq_of_adj_and_edgeSet_ncard_le__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:36:30.857262+00:00
-- url     : https://prove2.me/theorems/b519543a-3252-4892-b537-014b862f4f8f
-- title:
--   Equality from graph inclusion and reverse edge-count bound
-- statement:
--   If one finite graph contains another's edges and has no more edges, the two graphs are equal.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.eq_of_adj_and_edgeSet_ncard_le__p2m_4d05bb9d_42a1_4f6c_b6b4_be7b1a8f6d1e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V)
    (hsub : ∀ u v, H.Adj u v → K.Adj u v)
    (hcard : K.edgeSet.ncard ≤ H.edgeSet.ncard) :
    K = H := by sorry

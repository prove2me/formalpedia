-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_triangulation_supergraph__p2m_e072b4d5_a9ae_4f40_9238_0c277accf09b_a1
-- name    : WilliamsonShmoys.planar_connected_triangulation_supergraph__p2m_e072b4d5_a9ae_4f40_9238_0c277accf09b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:24:31.252052+00:00
-- url     : https://prove2.me/theorems/63a2cd28-190d-474c-9b63-884183b5c0a6
-- title:
--   Triangulated planar supergraph on the same vertices
-- statement:
--   Every connected finite simple graph with the supplied crossing-free drawing and at least three vertices has a planar supergraph on the same vertex set whose edge count is exactly three times the vertex count minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_triangulation_supergraph__p2m_e072b4d5_a9ae_4f40_9238_0c277accf09b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hConn : M.Connected)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V,
      M.edgeSet ⊆ N.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      N.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

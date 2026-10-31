-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound__p2m_6e30398e_7f8d_44b8_bb51_ffb2d64a0829_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_bound__p2m_6e30398e_7f8d_44b8_bb51_ffb2d64a0829_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:47:40.768014+00:00
-- url     : https://prove2.me/theorems/816757fd-0335-47c2-b0ba-1308329947fe
-- title:
--   Edge bound for an edge-maximal planar drawing
-- statement:
--   An edge-maximal drawable simple graph on at least three vertices has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_bound__p2m_6e30398e_7f8d_44b8_bb51_ffb2d64a0829_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ K : SimpleGraph V,
      M.edgeSet ⊆ K.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn K →
      K.edgeSet = M.edgeSet) :
    M.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

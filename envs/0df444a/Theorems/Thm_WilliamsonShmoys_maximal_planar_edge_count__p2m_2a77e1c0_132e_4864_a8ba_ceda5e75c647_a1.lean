-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2a77e1c0_132e_4864_a8ba_ceda5e75c647_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_2a77e1c0_132e_4864_a8ba_ceda5e75c647_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:58:29.89408+00:00
-- url     : https://prove2.me/theorems/3e24b586-e46a-433e-a6c0-ca887290c55d
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A finite connected inclusion-maximal simple planar graph with at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_2a77e1c0_132e_4864_a8ba_ceda5e75c647_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hconn : H.Connected)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

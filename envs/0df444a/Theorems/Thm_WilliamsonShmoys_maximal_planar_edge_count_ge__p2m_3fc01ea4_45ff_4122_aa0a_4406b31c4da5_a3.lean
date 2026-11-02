-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_ge__p2m_3fc01ea4_45ff_4122_aa0a_4406b31c4da5_a3
-- name    : WilliamsonShmoys.maximal_planar_edge_count_ge__p2m_3fc01ea4_45ff_4122_aa0a_4406b31c4da5_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:02:10.080326+00:00
-- url     : https://prove2.me/theorems/38e6d80b-f3ea-4425-9db3-0bd7e0773f7f
-- title:
--   Maximal planar graph edge-count lower bound
-- statement:
--   A connected, inclusion-maximal finite simple graph with a crossing-free drawing and at least three vertices has at least 3n − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count_ge__p2m_3fc01ea4_45ff_4122_aa0a_4406b31c4da5_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hHconn : H.Connected)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ J : SimpleGraph V, H ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     3 * Fintype.card V - 6 ≤ H.edgeFinset.card) := by
  sorry

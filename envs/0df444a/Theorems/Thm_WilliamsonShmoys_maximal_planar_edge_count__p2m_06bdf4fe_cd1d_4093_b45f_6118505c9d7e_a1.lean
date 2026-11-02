-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_06bdf4fe_cd1d_4093_b45f_6118505c9d7e_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_06bdf4fe_cd1d_4093_b45f_6118505c9d7e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:47:38.864432+00:00
-- url     : https://prove2.me/theorems/3fc01ea4-45ff-4122-aa0a-4406b31c4da5
-- title:
--   Edge count of an inclusion-maximal planar drawing
-- statement:
--   A connected, inclusion-maximal drawable simple graph on at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_06bdf4fe_cd1d_4093_b45f_6118505c9d7e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hHconn : H.Connected)
    (hHdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hHmax : ∀ J : SimpleGraph V, H ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_maximal_supergraph__p2m_06bdf4fe_cd1d_4093_b45f_6118505c9d7e_a1
-- name    : WilliamsonShmoys.planar_extension_maximal_supergraph__p2m_06bdf4fe_cd1d_4093_b45f_6118505c9d7e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:47:37.494262+00:00
-- url     : https://prove2.me/theorems/03fd7227-be52-409b-9f5b-92650e994dba
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every connected drawable graph in the finite simple-graph universe has a drawable supergraph on the same vertices that is maximal under inclusion. It remains connected, and its edge count is at least the original graph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_maximal_supergraph__p2m_06bdf4fe_cd1d_4093_b45f_6118505c9d7e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hKconn : K.Connected)
    (hKdraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       letI : DecidableRel H.Adj := Classical.decRel H.Adj
       K.edgeFinset.card ≤ H.edgeFinset.card) ∧
      H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (∀ J : SimpleGraph V, H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) := by
  sorry

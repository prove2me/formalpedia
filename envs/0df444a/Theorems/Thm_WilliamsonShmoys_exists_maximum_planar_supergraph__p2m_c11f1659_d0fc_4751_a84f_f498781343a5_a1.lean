-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximum_planar_supergraph__p2m_c11f1659_d0fc_4751_a84f_f498781343a5_a1
-- name    : WilliamsonShmoys.exists_maximum_planar_supergraph__p2m_c11f1659_d0fc_4751_a84f_f498781343a5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:55:20.787828+00:00
-- url     : https://prove2.me/theorems/5764801f-90c3-4af8-a11b-dee089324145
-- title:
--   A drawable graph has a maximum-edge drawable supergraph
-- statement:
--   Among the finitely many drawable simple graphs on the given finite vertex type, there is one with maximum edge count that contains the given drawable graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximum_planar_supergraph__p2m_c11f1659_d0fc_4751_a84f_f498781343a5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (dH : DecidableRel H.Adj)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeFinset ⊆ K.edgeFinset ∧
      ∀ (L : SimpleGraph V) (dL : DecidableRel L.Adj),
        WilliamsonShmoys.HasPlanarDrawingOn L →
        K.edgeFinset.card ≥ L.edgeFinset.card := by sorry

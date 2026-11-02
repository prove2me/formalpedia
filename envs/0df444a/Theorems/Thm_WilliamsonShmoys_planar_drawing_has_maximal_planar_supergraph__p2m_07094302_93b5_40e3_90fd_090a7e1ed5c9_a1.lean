-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_planar_supergraph__p2m_07094302_93b5_40e3_90fd_090a7e1ed5c9_a1
-- name    : WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_07094302_93b5_40e3_90fd_090a7e1ed5c9_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:36:43.292413+00:00
-- url     : https://prove2.me/theorems/010e34bf-16b2-404d-9a92-840753658b9f
-- title:
--   Extend a planar drawing to a maximal planar supergraph
-- statement:
--   Any drawable finite simple graph has a drawable supergraph on the same vertices that is maximal among drawable supergraphs under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph__p2m_07094302_93b5_40e3_90fd_090a7e1ed5c9_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        ∀ (J : SimpleGraph V), H ≤ J →
          WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H := by sorry

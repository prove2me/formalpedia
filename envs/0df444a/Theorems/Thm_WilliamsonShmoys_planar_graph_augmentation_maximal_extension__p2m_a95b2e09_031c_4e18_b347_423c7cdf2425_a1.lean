-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_augmentation_maximal_extension__p2m_a95b2e09_031c_4e18_b347_423c7cdf2425_a1
-- name    : WilliamsonShmoys.planar_graph_augmentation_maximal_extension__p2m_a95b2e09_031c_4e18_b347_423c7cdf2425_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T11:37:25.62759+00:00
-- url     : https://prove2.me/theorems/17a446e3-fee0-4c12-aad4-c95a1431715c
-- title:
--   Finite maximal planar extension
-- statement:
--   Every drawable connected graph on a finite ordered vertex type has a drawable connected supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_augmentation_maximal_extension__p2m_a95b2e09_031c_4e18_b347_423c7cdf2425_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hconn : H.Connected)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧ J.Connected ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧
      ∀ K : SimpleGraph V, J ≤ K →
        WilliamsonShmoys.HasPlanarDrawingOn K → K = J := by sorry

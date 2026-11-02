-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_adb36ea0_1077_447f_b2c5_a4177e2cdb6e_a1
-- name    : WilliamsonShmoys.planar_supergraph_maximal__p2m_adb36ea0_1077_447f_b2c5_a4177e2cdb6e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:32:15.214266+00:00
-- url     : https://prove2.me/theorems/1bbb274f-042a-4c5e-8e43-fd05505ca5a4
-- title:
--   Inclusion-maximal planar supergraph exists
-- statement:
--   Every drawable finite simple graph on V has a drawable supergraph that is inclusion-maximal among drawable supergraphs on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_maximal__p2m_adb36ea0_1077_447f_b2c5_a4177e2cdb6e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, HasPlanarDrawingOn K ∧
      (∀ u v, H.Adj u v → K.Adj u v) ∧
      (∀ L : SimpleGraph V, HasPlanarDrawingOn L →
        (∀ u v, K.Adj u v → L.Adj u v) →
        (∀ u v, L.Adj u v → K.Adj u v)) := by sorry

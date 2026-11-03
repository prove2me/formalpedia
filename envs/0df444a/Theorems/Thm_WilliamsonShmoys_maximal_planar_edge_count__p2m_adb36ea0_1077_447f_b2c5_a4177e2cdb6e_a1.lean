-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_adb36ea0_1077_447f_b2c5_a4177e2cdb6e_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_adb36ea0_1077_447f_b2c5_a4177e2cdb6e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:32:16.626215+00:00
-- url     : https://prove2.me/theorems/a0f5e8a0-e0da-456d-9ce8-2c77e5e78796
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_adb36ea0_1077_447f_b2c5_a4177e2cdb6e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hK : HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, HasPlanarDrawingOn L →
      (∀ u v, K.Adj u v → L.Adj u v) →
      (∀ u v, L.Adj u v → K.Adj u v)) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    3 * Fintype.card V = K.edgeFinset.card + 6 := by sorry

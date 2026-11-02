-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_augmentation__p2m_1dbaee3e_ce5f_437b_b54c_6804519e37e5_a1
-- name    : WilliamsonShmoys.maximal_planar_augmentation__p2m_1dbaee3e_ce5f_437b_b54c_6804519e37e5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:18:30.682209+00:00
-- url     : https://prove2.me/theorems/04185586-21f4-4990-a47b-2aac997e5516
-- title:
--   Maximal planar augmentation on a fixed vertex type
-- statement:
--   Every connected finite simple graph with at least three vertices and a crossing-free drawing has a planar supergraph on the same vertex type that is maximal among planar supergraphs, and the original graph’s edge count is no larger than the supergraph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_augmentation__p2m_1dbaee3e_ce5f_437b_b54c_6804519e37e5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hH : HasPlanarDrawingOn H) (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K) ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       letI : DecidableRel K.Adj := Classical.decRel K.Adj
       H.edgeFinset.card ≤ K.edgeFinset.card) := by sorry

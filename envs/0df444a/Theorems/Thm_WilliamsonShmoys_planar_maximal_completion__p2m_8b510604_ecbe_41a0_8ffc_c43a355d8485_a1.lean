-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_completion__p2m_8b510604_ecbe_41a0_8ffc_c43a355d8485_a1
-- name    : WilliamsonShmoys.planar_maximal_completion__p2m_8b510604_ecbe_41a0_8ffc_c43a355d8485_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:06.324456+00:00
-- url     : https://prove2.me/theorems/81eecf30-e96c-499d-b4eb-13964c396f7c
-- title:
--   Connected maximal planar completion
-- statement:
--   Every planar drawing on at least three vertices has a connected planar supergraph on the same vertices that is maximal among planar supergraphs and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_completion__p2m_8b510604_ecbe_41a0_8ffc_c43a355d8485_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel _
    ∃ H : SimpleGraph V,
      (letI : DecidableRel H.Adj := Classical.decRel _;
       G ≤ H ∧ H.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
       G.edgeFinset.card ≤ H.edgeSet.ncard ∧
       ∀ K : SimpleGraph V,
         (letI : DecidableRel K.Adj := Classical.decRel _;
          H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H)) := by sorry

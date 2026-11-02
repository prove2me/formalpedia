-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_ddf70dfc_9e43_42b2_878d_a461f3516711_a6
-- name    : WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ddf70dfc_9e43_42b2_878d_a461f3516711_a6
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:44:35.912146+00:00
-- url     : https://prove2.me/theorems/d9d03cd1-6b7b-408d-a4c7-f6600bd594e9
-- title:
--   Finite maximal drawable extension
-- statement:
--   Every drawable finite simple graph has a drawable supergraph on the same vertex type that is inclusion-maximal among drawable supergraphs, and whose edge count is at least that of the original graph. Finiteness of the set of simple graphs on V gives a proof by maximizing edge count; equality of edge counts under inclusion gives maximality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_maximal_extension__p2m_ddf70dfc_9e43_42b2_878d_a461f3516711_a6
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L = K) ∧
      (letI : DecidableRel H.Adj := Classical.decRel _
       letI : DecidableRel K.Adj := Classical.decRel _
       H.edgeFinset.card ≤ K.edgeFinset.card) := by
  sorry

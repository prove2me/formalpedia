-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_950f72dd_6d17_4b3b_8f95_2c20bcaaa4d7_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_950f72dd_6d17_4b3b_8f95_2c20bcaaa4d7_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:40:52.082826+00:00
-- url     : https://prove2.me/theorems/bc55d69b-5743-4927-884d-0327a4a2fa7c
-- title:
--   Edge count of an inclusion-maximal planar graph
-- statement:
--   A finite simple graph maximal among drawable supergraphs on its vertex set has exactly `3|V|−6` edges when it has at least three vertices. The condition excludes smaller cases where the formula need not hold. The proof route is to establish that maximality makes a planar embedding a triangulation, then apply Euler’s formula and count edge incidences on face boundaries. This is the core planar graph obligation left after the finite maximality step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_950f72dd_6d17_4b3b_8f95_2c20bcaaa4d7_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_has_maximal_supergraph__p2m_ed8fdf3f_bcec_42f4_9879_6d1c022759a1_a1
-- name    : WilliamsonShmoys.planarDrawing_has_maximal_supergraph__p2m_ed8fdf3f_bcec_42f4_9879_6d1c022759a1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:20:43.391624+00:00
-- url     : https://prove2.me/theorems/33e24dc2-9eae-41fb-a509-b23baf4724a2
-- title:
--   Maximal planar supergraph on a fixed finite vertex set
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertices that is maximal among planar supergraphs, and its edge count is at least the original graph’s.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_has_maximal_supergraph__p2m_ed8fdf3f_bcec_42f4_9879_6d1c022759a1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ HasPlanarDrawingOn K ∧ H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K := by sorry

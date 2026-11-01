-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_49e59269_0942_49a7_bb42_8d7dcf799486_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_49e59269_0942_49a7_bb42_8d7dcf799486_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:38:41.770232+00:00
-- url     : https://prove2.me/theorems/5770b3e4-2ec8-40d1-b3e9-07b1ee561228
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   A drawable simple graph on at least three finite linearly ordered vertices that admits no drawable supergraph on those vertices has exactly 3|U|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_49e59269_0942_49a7_bb42_8d7dcf799486_a1
    {U : Type} [Fintype U] [LinearOrder U]
    (K : SimpleGraph U) (hcard : 3 ≤ Fintype.card U)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph U, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → K = L) :
    3 * Fintype.card U - 6 = K.edgeSet.ncard := by
  sorry

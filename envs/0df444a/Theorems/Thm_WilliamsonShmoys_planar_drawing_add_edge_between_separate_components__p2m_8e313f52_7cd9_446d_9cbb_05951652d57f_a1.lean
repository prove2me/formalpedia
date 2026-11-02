-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_separate_components__p2m_8e313f52_7cd9_446d_9cbb_05951652d57f_a1
-- name    : WilliamsonShmoys.planar_drawing_add_edge_between_separate_components__p2m_8e313f52_7cd9_446d_9cbb_05951652d57f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T08:19:07.712116+00:00
-- url     : https://prove2.me/theorems/33838bec-6826-4ad5-baae-8ec51d932be6
-- title:
--   Planarity is preserved when bridging separate components
-- statement:
--   Given a planar drawing and vertices in distinct connected components, there is a planar drawing of a graph extending the original graph that includes an edge between those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_between_separate_components__p2m_8e313f52_7cd9_446d_9cbb_05951652d57f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    {u v : V} (hUnreachable : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ K.Adj u v ∧ WilliamsonShmoys.HasPlanarDrawingOn K := by
  sorry

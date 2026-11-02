-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_add_edge_of_not_reachable__p2m_889652c1_a82f_462e_b8d8_8391a5f102fc_a2
-- name    : WilliamsonShmoys.planarDrawing_add_edge_of_not_reachable__p2m_889652c1_a82f_462e_b8d8_8391a5f102fc_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:53:06.041426+00:00
-- url     : https://prove2.me/theorems/d7f1b006-c7a3-4d75-896f-59e453723319
-- title:
--   Add an edge between two components of a drawable graph
-- statement:
--   Given a planar drawing and two vertices in different components, add exactly their edge while retaining a planar drawing. The lemma makes the component-joining geometry reusable for any such pair.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem WilliamsonShmoys.planarDrawing_add_edge_of_not_reachable__p2m_889652c1_a82f_462e_b8d8_8391a5f102fc_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V)
    (huv : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      H.edgeSet = G.edgeSet ∪ {Sym2.mk u v} ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry

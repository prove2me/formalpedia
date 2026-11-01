-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_insertion__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
-- name    : WilliamsonShmoys_planar_edge_insertion__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:11:29.342768+00:00
-- url     : https://prove2.me/theorems/10eaf2f1-7409-4fae-95fa-e1e70a835601
-- title:
--   Insert one edge into a drawable graph below the planar bound
-- statement:
--   For a drawable simple graph on at least three vertices whose edge count is strictly below the planar maximum, add exactly one edge while retaining a planar drawing and the original graph as a subgraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys_planar_edge_insertion__p2m_d31de1f7_ef50_4693_bbf0_93f59f6d9afd_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V)
    (hE : G.edgeFinset.card < 3 * Fintype.card V - 6) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      G ≤ K ∧
      K.edgeFinset.card = G.edgeFinset.card + 1 := by sorry

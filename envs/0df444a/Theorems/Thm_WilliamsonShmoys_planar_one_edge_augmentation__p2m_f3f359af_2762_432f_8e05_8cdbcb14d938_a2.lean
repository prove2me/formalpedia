-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_one_edge_augmentation__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
-- name    : WilliamsonShmoys.planar_one_edge_augmentation__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T19:28:27.907357+00:00
-- url     : https://prove2.me/theorems/5fed2e6c-fc0c-4ddf-b02b-f52b48f84d02
-- title:
--   Add one edge below the planar maximum
-- statement:
--   If a drawable finite simple graph on at least three vertices has fewer than the planar maximum number of edges, one can add a single edge on the same vertex set while retaining a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_one_edge_augmentation__p2m_f3f359af_2762_432f_8e05_8cdbcb14d938_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hEdges : G.edgeSet.ncard < 3 * Fintype.card V - 6) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      H.edgeSet.ncard = G.edgeSet.ncard + 1 ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry

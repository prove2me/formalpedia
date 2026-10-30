-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_one_edge_insertion_of_card_ge_three__p2m_3d18ba84_dae9_4abe_9f72_3fa917a9726c_a3
-- name    : WilliamsonShmoys.planar_one_edge_insertion_of_card_ge_three__p2m_3d18ba84_dae9_4abe_9f72_3fa917a9726c_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:29:59.299878+00:00
-- url     : https://prove2.me/theorems/30cabda6-8091-40b2-a533-c24aec10a077
-- title:
--   Planar edge growth with at least three vertices
-- statement:
--   A disconnected graph on at least three vertices with a crossing-free drawing has a crossing-free supergraph on the same vertices with strictly more edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_one_edge_insertion_of_card_ge_three__p2m_3d18ba84_dae9_4abe_9f72_3fa917a9726c_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (hV : 3 <= Fintype.card V)
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hG_not_connected : ¬ G.Connected) :
    ∃ K : SimpleGraph V,
      G ≤ K ∧ HasPlanarDrawingOn K ∧
      G.edgeSet.ncard < K.edgeSet.ncard := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_maximal_drawable_has_euler_edge_count__p2m_f1c5cd14_5ded_4838_bd8a_1ed332d55054_a1
-- name    : WilliamsonShmoys.edge_maximal_drawable_has_euler_edge_count__p2m_f1c5cd14_5ded_4838_bd8a_1ed332d55054_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:09:50.175888+00:00
-- url     : https://prove2.me/theorems/b4c9393f-ee8c-44c0-9df7-8513af7ec896
-- title:
--   Edge-maximal drawable graph has the Euler edge count
-- statement:
--   A drawable graph on at least three finite linearly ordered vertices that is maximal among drawable supergraphs on those vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_maximal_drawable_has_euler_edge_count__p2m_f1c5cd14_5ded_4838_bd8a_1ed332d55054_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hMax : ∀ (K : SimpleGraph V) [DecidableRel K.Adj],
      H.edgeFinset ⊆ K.edgeFinset → HasPlanarDrawingOn K →
        K.edgeFinset ⊆ H.edgeFinset)
    (hV : 3 <= Fintype.card V) :
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry

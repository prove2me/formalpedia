-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_maximal_edge_count_3n_minus_6__p2m_5a949825_f81a_4c8d_a9c0_487ac649892b_a3
-- name    : WilliamsonShmoys.planar_edge_maximal_edge_count_3n_minus_6__p2m_5a949825_f81a_4c8d_a9c0_487ac649892b_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T23:05:37.809546+00:00
-- url     : https://prove2.me/theorems/727657a6-98ce-4392-ad63-d05814912170
-- title:
--   An edge-maximal drawable simple graph has the planar extremal edge count
-- statement:
--   A drawable simple graph on at least three vertices that has no strictly larger drawable supergraph on the same vertices has exactly 3n−6 edges. This isolates the maximal-planar characterization needed after choosing a finite maximal extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_maximal_edge_count_3n_minus_6__p2m_5a949825_f81a_4c8d_a9c0_487ac649892b_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V) (hDraw : HasPlanarDrawingOn X)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ Y : SimpleGraph V, X ≤ Y → HasPlanarDrawingOn Y → Y = X) :
    X.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_e592f479_7758_40c0_97f7_ee5e29c0fee3_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_e592f479_7758_40c0_97f7_ee5e29c0fee3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:24:50.848128+00:00
-- url     : https://prove2.me/theorems/cf161613-a0bb-4259-95d5-c320f30b7319
-- title:
--   Maximal drawable graphs meet the planar edge lower bound
-- statement:
--   For a drawable graph on at least three vertices, maximality among drawable supergraphs on the same vertices forces at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_e592f479_7758_40c0_97f7_ee5e29c0fee3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V, M ≤ N → WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    3 * Fintype.card V - 6 ≤ M.edgeSet.ncard := by sorry

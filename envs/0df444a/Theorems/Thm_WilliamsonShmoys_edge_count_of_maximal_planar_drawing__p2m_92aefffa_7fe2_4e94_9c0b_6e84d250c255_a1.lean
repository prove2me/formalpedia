-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing__p2m_92aefffa_7fe2_4e94_9c0b_6e84d250c255_a1
-- name    : WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_92aefffa_7fe2_4e94_9c0b_6e84d250c255_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T13:02:40.322049+00:00
-- url     : https://prove2.me/theorems/3ca4615a-eebc-4af0-940e-7aeb5834c3ad
-- title:
--   Edge count of an edge-maximal planar drawing
-- statement:
--   An edge-maximal crossing-free drawing of a finite simple graph with at least three vertices has exactly 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_92aefffa_7fe2_4e94_9c0b_6e84d250c255_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ M' : SimpleGraph V, HasPlanarDrawingOn M' → M ≤ M' → M' = M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry

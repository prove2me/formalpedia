-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:04:21.770882+00:00
-- url     : https://prove2.me/theorems/83d9f0a5-b086-4e9a-82e5-51c146823d01
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   An edge-maximal graph admitting a crossing-free drawing on at least three vertices has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_6f6a4225_6fc3_4c15_be9a_75786ea7ae4b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hH : HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    letI : (G : SimpleGraph V) -> DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    H.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry

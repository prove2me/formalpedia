-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_dcda2b2e_bb79_4b65_906a_4b43dfb1e747_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_dcda2b2e_bb79_4b65_906a_4b43dfb1e747_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:45:57.975513+00:00
-- url     : https://prove2.me/theorems/92aefffa-7fe2-4e94-9c0b-6e84d250c255
-- title:
--   Edge upper bound for a drawable graph
-- statement:
--   Every graph with the supplied crossing-free drawing on at least three vertices has at most three times the number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_dcda2b2e_bb79_4b65_906a_4b43dfb1e747_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_017fa3bd_a11a_42f0_a60e_fe3ebb157a5f_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_017fa3bd_a11a_42f0_a60e_fe3ebb157a5f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T08:24:43.521823+00:00
-- url     : https://prove2.me/theorems/316bc1de-e9dc-4c0b-bf6c-1bec8a5e1bc5
-- title:
--   Planar drawing edge upper bound
-- statement:
--   A simple graph with the supplied crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_017fa3bd_a11a_42f0_a60e_fe3ebb157a5f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
     M.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry

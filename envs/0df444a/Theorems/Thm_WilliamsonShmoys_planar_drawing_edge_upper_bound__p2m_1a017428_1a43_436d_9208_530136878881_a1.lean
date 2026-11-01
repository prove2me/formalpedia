-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_1a017428_1a43_436d_9208_530136878881_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_1a017428_1a43_436d_9208_530136878881_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:40:18.103335+00:00
-- url     : https://prove2.me/theorems/e4f60b04-c635-4cd7-9005-1b8d26489bf8
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Any drawable simple graph on at least three finite vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_1a017428_1a43_436d_9208_530136878881_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel L.Adj := Classical.decRel L.Adj
     L.edgeFinset.card <= 3 * Fintype.card V - 6) := by sorry

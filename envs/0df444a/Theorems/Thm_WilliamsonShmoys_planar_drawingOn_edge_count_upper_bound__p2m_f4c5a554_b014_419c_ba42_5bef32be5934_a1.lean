-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_count_upper_bound__p2m_f4c5a554_b014_419c_ba42_5bef32be5934_a1
-- name    : WilliamsonShmoys.planar_drawingOn_edge_count_upper_bound__p2m_f4c5a554_b014_419c_ba42_5bef32be5934_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:44:58.678396+00:00
-- url     : https://prove2.me/theorems/fab89fb1-e873-4b82-98f3-cd1985d7426b
-- title:
--   Edge bound for a graph with a planar drawing
-- statement:
--   For a simple graph with the specified planar drawing and at least three vertices, the number of edges is at most three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawingOn_edge_count_upper_bound__p2m_f4c5a554_b014_419c_ba42_5bef32be5934_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hPlanar : HasPlanarDrawingOn K) :
    letI : DecidableRel K.Adj := Classical.decRel K.Adj
    K.edgeFinset.card + 6 <= 3 * Fintype.card V := by sorry

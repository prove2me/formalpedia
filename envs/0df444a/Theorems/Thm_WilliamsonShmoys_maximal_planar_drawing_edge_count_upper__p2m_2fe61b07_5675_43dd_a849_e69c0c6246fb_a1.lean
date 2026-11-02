-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_upper__p2m_2fe61b07_5675_43dd_a849_e69c0c6246fb_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count_upper__p2m_2fe61b07_5675_43dd_a849_e69c0c6246fb_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T15:30:31.677112+00:00
-- url     : https://prove2.me/theorems/2d3691ae-6dd7-4b0b-bd09-07516f5319a3
-- title:
--   Planar drawing edge upper bound
-- statement:
--   Every simple graph with the specified crossing-free drawing and at least three vertices has at most `3|V| - 6` edges. This child removes the universal upper-bound part of the parent count; it follows by Euler’s formula and face-degree counting, with disconnected components handled separately or connected by added arcs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count_upper__p2m_2fe61b07_5675_43dd_a849_e69c0c6246fb_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    letI : DecidableRel N.Adj := Classical.decRel N.Adj
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by sorry

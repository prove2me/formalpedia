-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_050d6eed_4305_48ca_94b0_9518ffa2e96b_a3
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound__p2m_050d6eed_4305_48ca_94b0_9518ffa2e96b_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:32:34.891908+00:00
-- url     : https://prove2.me/theorems/4a772063-d306-45bd-a029-619aef07cba4
-- title:
--   Planar edge count upper bound
-- statement:
--   Every finite simple graph with a drawing satisfying `HasPlanarDrawingOn` and at least three vertices has at most `3|V| - 6` edges. This removes the planar upper-bound work from the parent. A proof route is to connect components by noncrossing arcs, use Euler's formula for a plane embedding, and count edge-face incidences, with each face boundary having length at least three in the resulting simple planar graph. The condition `|V| >= 3` includes the smallest allowed case and is needed for the face-length bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_bound__p2m_050d6eed_4305_48ca_94b0_9518ffa2e96b_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (T : SimpleGraph V)
    (hT : HasPlanarDrawingOn T)
    (hV : 3 <= Fintype.card V) :
    T.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  sorry

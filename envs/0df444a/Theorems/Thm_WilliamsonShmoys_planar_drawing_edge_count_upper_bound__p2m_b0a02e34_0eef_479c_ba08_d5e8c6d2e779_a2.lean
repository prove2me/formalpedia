-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T00:47:30.469978+00:00
-- url     : https://prove2.me/theorems/58d8e6f3-93b9-4006-85ea-c7e3275fd746
-- title:
--   Edge count upper bound for a planar drawing
-- statement:
--   Every finite simple graph with at least three vertices and a drawing satisfying `HasPlanarDrawingOn` has at most `3 |V| - 6` edges. Prove this independently by deriving a plane embedding from the arcs, applying Euler’s formula, and counting edge-face incidences, with simplicity and the size hypothesis handling small-face cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_b0a02e34_0eef_479c_ba08_d5e8c6d2e779_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  sorry

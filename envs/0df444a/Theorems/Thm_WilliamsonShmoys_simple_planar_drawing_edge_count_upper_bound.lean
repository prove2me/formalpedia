-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_drawing_edge_count_upper_bound
-- name    : WilliamsonShmoys.simple_planar_drawing_edge_count_upper_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T05:18:39.066542+00:00
-- url     : https://prove2.me/theorems/2745a595-6083-4e4f-a41e-88c5cf3d089b
-- title:
--   Euler edge bound for a drawable simple graph
-- statement:
--   Every graph with the specified crossing-free drawing and at least three vertices has at most 3|V|−6 edges. This supplies the target’s upper bound; one proof route derives a planar embedding and applies Euler’s inequality, treating components as needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.simple_planar_drawing_edge_count_upper_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_219c2427_f0ca_410a_8cab_2194ee3f8b9c
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_219c2427_f0ca_410a_8cab_2194ee3f8b9c
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:14:26.222174+00:00
-- url     : https://prove2.me/theorems/8234d27e-60d0-438d-b81b-93ea7885828b
-- title:
--   Edge bound for a finite planar drawing
-- statement:
--   A finite graph with a crossing-free drawing and at least three vertices has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_219c2427_f0ca_410a_8cab_2194ee3f8b9c
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

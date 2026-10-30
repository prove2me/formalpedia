-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_38a90fc3_dea3_4c9f_8a52_b5002f138593_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_38a90fc3_dea3_4c9f_8a52_b5002f138593_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T23:14:24.920491+00:00
-- url     : https://prove2.me/theorems/ef7acfeb-d97d-47d2-a77f-a6410accbe74
-- title:
--   Euler edge bound for a finite graph with a planar drawing
-- statement:
--   Every finite simple graph with at least three vertices that admits the specified crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_38a90fc3_dea3_4c9f_8a52_b5002f138593_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  sorry

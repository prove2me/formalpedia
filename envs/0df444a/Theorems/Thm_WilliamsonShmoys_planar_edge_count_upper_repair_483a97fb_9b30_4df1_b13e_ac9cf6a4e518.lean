-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- name    : WilliamsonShmoys.planar_edge_count_upper_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T10:43:47.81717+00:00
-- url     : https://prove2.me/theorems/bc720b29-f8f8-449c-89d1-8134f93ed2bf
-- title:
--   Planar drawing edge-count upper bound
-- statement:
--   A graph with the specified crossing-free drawing on at least three finite vertices has at most 3|V| − 6 edges. Euler’s formula and simplicity provide the upper bound; the vertex threshold is retained for the small-graph boundary.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_count_upper_repair_483a97fb_9b30_4df1_b13e_ac9cf6a4e518
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hGdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

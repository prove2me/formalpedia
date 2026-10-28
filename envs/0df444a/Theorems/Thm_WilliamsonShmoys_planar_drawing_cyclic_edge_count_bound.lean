-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_cyclic_edge_count_bound
-- name    : WilliamsonShmoys.planar_drawing_cyclic_edge_count_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:36:38.845202+00:00
-- url     : https://prove2.me/theorems/479c1166-2ea4-40b5-b7df-4149a6615f1e
-- title:
--   Planar edge bound for a connected cyclic drawing
-- statement:
--   A finite connected simple graph with a cycle and a crossing-free drawing satisfies the planar edge bound. The cycle ensures the usual bound applies in the range of at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_cyclic_edge_count_bound
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hConnected : G.Connected)
    (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCyclic : ¬ G.IsAcyclic) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

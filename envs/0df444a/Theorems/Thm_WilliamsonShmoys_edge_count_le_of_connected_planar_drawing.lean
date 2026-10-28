-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_le_of_connected_planar_drawing
-- name    : WilliamsonShmoys.edge_count_le_of_connected_planar_drawing
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T08:21:15.704094+00:00
-- url     : https://prove2.me/theorems/eeec8123-4de2-4c0f-820e-1902d3cbaa98
-- title:
--   Planar edge bound for connected drawings
-- statement:
--   A connected graph with a crossing-free drawing on at least three vertices has at most `3n − 6` edges. This contains the main topological work. A proof route is to extend the embedding to a triangulation without adding vertices, apply Euler’s formula and count face-edge incidences; the triangulation step handles bridges and faces whose original boundary walks are short.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.edge_count_le_of_connected_planar_drawing
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry

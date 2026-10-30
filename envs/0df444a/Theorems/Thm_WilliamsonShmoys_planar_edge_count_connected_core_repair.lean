-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_connected_core_repair
-- name    : WilliamsonShmoys.planar_edge_count_connected_core_repair
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:53:23.399136+00:00
-- url     : https://prove2.me/theorems/ff4aa18e-3454-44b7-a1a0-16ab45dfa62e
-- title:
--   Euler edge bound for a connected drawable simple graph
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges. The proof uses Euler’s formula and counts facial boundary incidences, accounting for the short-walk cases allowed by the drawing representation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_connected_core_repair
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by sorry

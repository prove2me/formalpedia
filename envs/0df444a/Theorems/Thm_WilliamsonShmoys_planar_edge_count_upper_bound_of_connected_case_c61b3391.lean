-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_of_connected_case_c61b3391
-- name    : WilliamsonShmoys.planar_edge_count_upper_bound_of_connected_case_c61b3391
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T10:09:07.640484+00:00
-- url     : https://prove2.me/theorems/b2dabfba-8b88-471d-b266-4daa28cbf480
-- title:
--   Assemble the planar edge bound from connected cases
-- statement:
--   If the planar edge bound holds for every connected finite simple graph with at least three vertices, then it holds for every finite simple graph with a crossing-free drawing and at least three vertices. Reduce to induced connected components, restrict the drawing to each component, bound components of size one or two directly, and sum the edge counts.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_count_upper_bound_of_connected_case_c61b3391
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConnectedBound : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (H : SimpleGraph W),
      3 ≤ Fintype.card W →
      H.Connected →
      WilliamsonShmoys.HasPlanarDrawingOn H →
      H.edgeSet.ncard ≤ 3 * Fintype.card W - 6) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry

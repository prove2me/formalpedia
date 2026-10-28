-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound_of_connected_case
-- name    : WilliamsonShmoys.planar_drawingOn_edge_bound_of_connected_case
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:22:46.823217+00:00
-- url     : https://prove2.me/theorems/9ad3c081-03ba-4c2c-9b7b-868d66610b43
-- title:
--   Reduce the planar edge bound to connected graphs
-- statement:
--   For a finite drawn simple graph with at least three vertices, the sharp edge bound follows if it holds for every connected finite drawn simple graph with at least three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_edge_bound_of_connected_case
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hConnectedBound :
      ∀ {W : Type} [Fintype W] [LinearOrder W] (G : SimpleGraph W),
        WilliamsonShmoys.HasPlanarDrawingOn G → G.Connected →
        3 ≤ Fintype.card W →
        G.edgeSet.ncard ≤ 3 * Fintype.card W - 6) :
    K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry

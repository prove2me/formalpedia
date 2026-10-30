-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_extension_core
-- name    : WilliamsonShmoys.planar_drawing_edge_bound_extension_core
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:47:06.734855+00:00
-- url     : https://prove2.me/theorems/8a86a385-3152-4dd6-bf92-62267c650f8a
-- title:
--   Tight planar extension for the simple planar edge bound
-- statement:
--   Extend a connected finite simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn to a graph on the same vertices with exactly 3n−6 edges, retaining every original edge.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound_extension_core
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry

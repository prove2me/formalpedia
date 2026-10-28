-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_local_edge_extension
-- name    : WilliamsonShmoys.planar_drawing_local_edge_extension
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T22:56:38.120645+00:00
-- url     : https://prove2.me/theorems/e694d678-427d-4f2d-9826-82eab672616e
-- title:
--   Add an edge to a disconnected planar drawing
-- statement:
--   Any disconnected finite graph with a drawing as defined by `HasPlanarDrawingOn` admits a planar supergraph on the same vertices with at least one new edge. A proof can choose two distinct components incident to a common face and draw a simple joining arc through that face, so it avoids all existing edge interiors and vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_local_edge_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hNotConn : ¬ H.Connected) :
    ∃ L : SimpleGraph V, H ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      ∃ u v : V, L.Adj u v ∧ ¬ H.Adj u v := by sorry

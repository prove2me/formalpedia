-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_step
-- name    : WilliamsonShmoys.planar_drawing_connected_step
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-27T01:30:15.824983+00:00
-- url     : https://prove2.me/theorems/12e52f6d-6f68-4be3-bc59-6b71ceee8b6f
-- title:
--   Add a planar edge between disconnected components
-- statement:
--   Any disconnected finite graph with the supplied planar drawing has a planar supergraph on the same vertices that adds an edge between two previously unreachable vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_step
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∃ u v, ¬ G.Reachable u v ∧ H.Adj u v := by sorry

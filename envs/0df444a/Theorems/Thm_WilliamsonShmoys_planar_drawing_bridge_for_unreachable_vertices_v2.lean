-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_bridge_for_unreachable_vertices_v2
-- name    : WilliamsonShmoys.planar_drawing_bridge_for_unreachable_vertices_v2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T06:44:17.209042+00:00
-- url     : https://prove2.me/theorems/f6d1023a-7949-4701-bae5-734b9d81926e
-- title:
--   Add a drawable bridge between fixed unreachable vertices
-- statement:
--   For a crossing-free drawing and two unreachable fixed vertices, one can add an edge between them while retaining a crossing-free drawing on the same vertex type. The intended argument uses a common face of the disconnected components to draw a connecting arc.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_bridge_for_unreachable_vertices_v2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (u v : V)
    (hUnreachable : ¬ K.Reachable u v) :
    ∃ H : SimpleGraph V,
      K ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧ H.Adj u v := by sorry

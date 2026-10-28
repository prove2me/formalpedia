-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_completion_same_vertices_v4
-- name    : WilliamsonShmoys.planar_drawing_connected_completion_same_vertices_v4
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:12:16.381216+00:00
-- url     : https://prove2.me/theorems/7679e9be-3487-4650-a4d7-b88de73b2bea
-- title:
--   Connected completion of a drawable graph with at least three vertices
-- statement:
--   A drawable finite simple graph on at least three vertices can be extended on the same vertex type to a connected graph that still has a planar drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_completion_same_vertices_v4
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ J : SimpleGraph V, H ≤ J ∧
      WilliamsonShmoys.HasPlanarDrawingOn J ∧ J.Connected := by sorry

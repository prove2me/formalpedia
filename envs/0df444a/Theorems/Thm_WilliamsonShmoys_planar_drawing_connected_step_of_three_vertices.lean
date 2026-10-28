-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_step_of_three_vertices
-- name    : WilliamsonShmoys.planar_drawing_connected_step_of_three_vertices
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T09:17:29.188451+00:00
-- url     : https://prove2.me/theorems/d2c8621e-d551-4e15-a503-9876bdc56d4f
-- title:
--   Join disconnected components of a finite planar drawing
-- statement:
--   A disconnected finite graph with at least three vertices and a drawing satisfying the supplied crossing-free arc conditions has a planar supergraph on the same vertices that adds an edge between two previously unreachable vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_connected_step_of_three_vertices
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V)
    (hDisconnected : ¬ G.Connected) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ HasPlanarDrawingOn H ∧
      ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v := by sorry

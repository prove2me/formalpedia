-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_simple_edge_bound_from_embedding
-- name    : WilliamsonShmoys.planar_drawing_simple_edge_bound_from_embedding
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:12:20.77901+00:00
-- url     : https://prove2.me/theorems/3a56e81a-25fa-4f93-9f9a-be45665c79be
-- title:
--   Simple planar graph edge bound
-- statement:
--   A connected simple graph with at least three vertices and a crossing-free drawing has at most three times its vertex count minus six edges, expressed without truncated natural subtraction.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_simple_edge_bound_from_embedding
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : G.Connected)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry

-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_fdf6b599_6bc6_49f9_8e7c_aa4a3539064a_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_fdf6b599_6bc6_49f9_8e7c_aa4a3539064a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:35:46.599944+00:00
-- url     : https://prove2.me/theorems/ff0df929-a528-472b-801c-6c58169000bb
-- title:
--   Edge bound for a connected simple planar drawing
-- statement:
--   For a connected simple graph on at least three vertices with a crossing-free drawing, the number of edges plus six is at most three times the number of vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_fdf6b599_6bc6_49f9_8e7c_aa4a3539064a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hcard : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry

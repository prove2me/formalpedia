-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound__p2m_8cec4366_35b2_432d_b040_b53e5778430a_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_bound__p2m_8cec4366_35b2_432d_b040_b53e5778430a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:21:07.689668+00:00
-- url     : https://prove2.me/theorems/d11f956e-1f62-462c-aaa0-9c66268033aa
-- title:
--   Edge bound for a connected simple planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices that admits the specified crossing-free drawing has at most three times its number of vertices minus six edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_bound__p2m_8cec4366_35b2_432d_b040_b53e5778430a_a1 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) (hconn : T.Connected) : T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

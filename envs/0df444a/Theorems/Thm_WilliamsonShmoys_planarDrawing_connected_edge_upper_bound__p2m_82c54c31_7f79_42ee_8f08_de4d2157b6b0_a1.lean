-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawing_connected_edge_upper_bound__p2m_82c54c31_7f79_42ee_8f08_de4d2157b6b0_a1
-- name    : WilliamsonShmoys.planarDrawing_connected_edge_upper_bound__p2m_82c54c31_7f79_42ee_8f08_de4d2157b6b0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T05:53:55.456307+00:00
-- url     : https://prove2.me/theorems/dda84c13-d09c-47b5-b038-703e6ce3c995
-- title:
--   Edge bound for a connected planar drawing
-- statement:
--   A finite connected simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has at most 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planarDrawing_connected_edge_upper_bound__p2m_82c54c31_7f79_42ee_8f08_de4d2157b6b0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hV : 3 ≤ Fintype.card V) :
    K.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by sorry

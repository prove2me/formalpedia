-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1
-- name    : WilliamsonShmoys.planar_connected_edge_count__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:14:45.668542+00:00
-- url     : https://prove2.me/theorems/3a51fbaa-32ff-4069-a4cd-a20e0ddd155e
-- title:
--   Edge bound for connected drawn graphs
-- statement:
--   A finite connected simple graph with at least three vertices and a drawing satisfying HasPlanarDrawingOn has at most 3n−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_edge_count__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 <= Fintype.card V) :
    G.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry

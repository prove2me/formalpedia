-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_connected_planar_edge_range__p2m_a5ca72a9_ecf9_4fb7_a47f_154e4f49a23b_a5
-- name    : WilliamsonShmoys.simple_connected_planar_edge_range__p2m_a5ca72a9_ecf9_4fb7_a47f_154e4f49a23b_a5
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T01:58:14.781064+00:00
-- url     : https://prove2.me/theorems/7da2409a-cbf1-4fa5-b632-5ead272fc49b
-- title:
--   Edge range for a connected simple planar graph
-- statement:
--   For a connected simple graph with at least three vertices and a crossing-free drawing, the edge count lies between |V|−1 and 3|V|−6. The lower bound follows from a spanning tree; the upper bound follows from the Euler face count and the fact that every facial walk has length at least three.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.simple_connected_planar_edge_range__p2m_a5ca72a9_ecf9_4fb7_a47f_154e4f49a23b_a5
    {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V)
    (hdraw : HasPlanarDrawingOn T) (hconn : T.Connected)
    (hV : 3 ≤ Fintype.card V) :
    T.edgeSet.ncard + 6 ≤ 3 * Fintype.card V ∧
      Fintype.card V ≤ T.edgeSet.ncard + 1 := by sorry

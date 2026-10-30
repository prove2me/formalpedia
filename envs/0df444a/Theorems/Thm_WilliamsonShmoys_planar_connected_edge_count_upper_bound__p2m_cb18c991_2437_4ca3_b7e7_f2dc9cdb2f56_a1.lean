-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_connected_edge_count_upper_bound__p2m_cb18c991_2437_4ca3_b7e7_f2dc9cdb2f56_a1
-- name    : WilliamsonShmoys.planar_connected_edge_count_upper_bound__p2m_cb18c991_2437_4ca3_b7e7_f2dc9cdb2f56_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:06:36.707063+00:00
-- url     : https://prove2.me/theorems/dd205c68-bd0c-441d-ba83-4d0ce58e6ad4
-- title:
--   Euler edge bound for a connected planar drawing
-- statement:
--   A connected finite simple graph with at least three vertices and the specified crossing-free drawing has at most 3|V| − 6 edges. This isolates the Euler and triangulation argument from the target's disconnected case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_connected_edge_count_upper_bound__p2m_cb18c991_2437_4ca3_b7e7_f2dc9cdb2f56_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) (hConnected : K.Connected) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by sorry

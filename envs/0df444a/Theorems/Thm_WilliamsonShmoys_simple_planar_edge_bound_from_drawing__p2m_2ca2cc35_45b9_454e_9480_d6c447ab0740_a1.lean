-- Prove2me | Theorems.Thm_WilliamsonShmoys_simple_planar_edge_bound_from_drawing__p2m_2ca2cc35_45b9_454e_9480_d6c447ab0740_a1
-- name    : WilliamsonShmoys.simple_planar_edge_bound_from_drawing__p2m_2ca2cc35_45b9_454e_9480_d6c447ab0740_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:35:37.349501+00:00
-- url     : https://prove2.me/theorems/cd539f9d-43c0-4104-8907-5b455d63330b
-- title:
--   Simple planar edge bound from a drawing
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing has at most 3|V|−6 edges. This is the central topological consequence needed by the parent; the lower boundary n=3 yields at most three edges, which is sharp for a triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.simple_planar_edge_bound_from_drawing__p2m_2ca2cc35_45b9_454e_9480_d6c447ab0740_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    (letI : DecidableRel H.Adj := Classical.decRel H.Adj
     H.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by sorry
